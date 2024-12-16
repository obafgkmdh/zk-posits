package posit

import (
	"math/big"
	"math/bits"

	"github.com/consensys/gnark/frontend"

	"gnark-float/gadget"
	"gnark-float/hint"
	"gnark-float/util"
)

type Context struct {
	Api          frontend.API
	Gadget       *gadget.IntGadget
	N            uint // Number of bits
	LOGN         uint // Bitlength of N
	M            uint // Maximum number of bits for the mantissa
	ES           uint // Number of exponent bits
	ONES_REGIME  uint // (N - 2) + (N - 1)
	MAX_E        *big.Int // 2^ES
}

type PositVar struct {
	Sign frontend.Variable
	// Regime is biased by N-1
	Regime frontend.Variable
	Exponent frontend.Variable
	// We store the mantissa as if it had N-3-ES bits of precision.
	// Leading 1 is included, so we add 2^(N-3-ES)
	Mantissa frontend.Variable
}

func NewContext(api frontend.API, range_size uint, N uint, ES uint) Context {
	MAX_E := new(big.Int).Lsh(big.NewInt(1), ES)
	M := N - 3 - ES
	LOGN := uint(bits.Len(N))
	pow2_size := N
	return Context{
		Api:          api,
		Gadget:       gadget.NewWithEFBits(api, range_size, pow2_size, N, ES),
		N:            N,
		LOGN:         LOGN,
		M:            M,
		ES:           ES,
		ONES_REGIME:  2 * N - 3,
		MAX_E:        MAX_E,
	}
}


func (f *Context) efbits(k frontend.Variable) (frontend.Variable, frontend.Variable, frontend.Variable, frontend.Variable) {
	return f.Gadget.QueryEFBits(k, f.N, f.ES)
}

// Allocate a variable in the constraint system from a value.
// This function decomposes the value into sign, regime, exponent, and fraction,
// and enforces they are well-formed.
func (f *Context) NewPosit(v frontend.Variable) PositVar {
	// Extract sign, exponent, and mantissa from the value
	outputs, err := f.Api.Compiler().NewHint(hint.DecodePositHint, 4, v, f.N, f.ES)
	if err != nil {
		panic(err)
	}
	s := outputs[0]
	k := outputs[1]
	e := outputs[2]
	fr := outputs[3]

	f.Api.AssertIsBoolean(s)

	zero_regime := f.Api.IsZero(k)
	ones_regime := f.Gadget.IsEq(k, f.ONES_REGIME)

	ebits, fbits, eshift, fshift := f.efbits(k)
	k_is_neg := f.Gadget.IsEq(f.Api.Add(ebits, fbits, 1), k) // 0 < k <= N-2
	efshift := f.Api.Mul(eshift, fshift)

	// regime bits shifted to the correct location
	// if zero_regime, this equals v
	INF := new(big.Int).Lsh(big.NewInt(1), f.N - 1)
	regime_shifted := f.Api.Select(
		zero_regime,
		f.Api.Mul(s, INF),
		f.Api.Select(
			k_is_neg,
			1,
			f.Api.Sub(f.Api.DivUnchecked(INF, efshift), f.Api.Sub(2, ones_regime)),
	))

	mantissa_msb := new(big.Int).Lsh(big.NewInt(1), f.M)
	regime_shifted_2 := f.Api.Mul(regime_shifted, f.MAX_E, mantissa_msb)
	exponent_shifted := f.Api.DivUnchecked(f.Api.Mul(e, f.MAX_E), eshift)
	fraction_shifted := f.Api.Mul(fr, f.Api.DivUnchecked(mantissa_msb, fshift))

	v_comp := f.Api.Select(s, f.Api.Sub(new(big.Int).Lsh(big.NewInt(1), f.N), v), v)

	f.Api.AssertIsEqual(
		f.Api.Mul(f.Api.Add(regime_shifted_2, f.Api.Mul(exponent_shifted, mantissa_msb), fraction_shifted), efshift),
		f.Api.Mul(v_comp, f.MAX_E, mantissa_msb))

	// Enforce the bit length of exponent and mantissa
	// Regime bit length is already enforced by the lookup table
	f.Gadget.AssertBitLength(e, f.ES, gadget.TightForSmallAbs)
	f.Gadget.AssertBitLength(fr, f.M, gadget.TightForSmallAbs)

	return PositVar{
		Sign:       s,
		Regime:     k,
		Exponent:   exponent_shifted,
		Mantissa:   f.Api.Add(f.Api.Mul(f.Api.Sub(1, zero_regime), mantissa_msb), fraction_shifted),
	}
}

// Allocate a constant in the constraint system.
func (f *Context) NewConstant(v uint64) PositVar {
	components := util.PositComponentsOf(v, uint64(f.N), uint64(f.ES))

	return PositVar{
		Sign:       components[0],
		Regime:     components[1],
		Exponent:   components[2],
		Mantissa:   components[3],
	}
}

// Enforce the equality between two numbers.
func (f *Context) AssertIsEqual(x, y PositVar) {
	//f.Api.Println(x.Sign, x.Regime, x.Exponent, x.Mantissa)
	//f.Api.Println(y.Sign, y.Regime, y.Exponent, y.Mantissa)
	f.Api.AssertIsEqual(x.Sign, y.Sign)
	f.Api.AssertIsEqual(x.Regime, y.Regime)
	f.Api.AssertIsEqual(x.Exponent, y.Exponent)
	f.Api.AssertIsEqual(x.Mantissa, y.Mantissa)
}

// Round mantissa and decompose exponent, fixing overflow as needed.
// Mantissa should have less than mantissa_bit_length bits, MSB is assumed unless zero_mantissa
// Exponent should be correctly biased (i.e., (k + N-1) * 2^ES + e)
// Returns: rounded mantissa, biased regime, rounded exponent
func (f *Context) round(
	mantissa frontend.Variable,
	zero_mantissa frontend.Variable,
	mantissa_bit_length uint,
	exponent frontend.Variable,
) (frontend.Variable, frontend.Variable, frontend.Variable) {
	f.Api.Compiler().MarkBoolean(zero_mantissa)
	mantissa_low := new(big.Int).Lsh(big.NewInt(1), mantissa_bit_length - 1)

	// decompose exponent = regime * 2^ES + e, where e is in [0, MAX_E)
	outputs, err := f.Api.Compiler().NewHint(hint.TruncHint, 1, exponent, f.ES)
	if err != nil {
		panic(err)
	}
	regime := outputs[0]
	e := f.Api.Sub(exponent, f.Api.Mul(regime, f.MAX_E))
	f.Gadget.AssertBitLength(e, f.ES, gadget.TightForSmallAbs)

	ebits, fbits, eshift, fshift := f.efbits(regime)
	efshift := f.Api.Mul(eshift, fshift)

	// Depending on the regime, either the exponent or mantissa needs to be rounded.
	// To avoid rounding twice, we do rounding on regime || exponent || mantissa, where mantissa has its MSB removed
	combined_e_m := f.Api.Select(
		zero_mantissa,
		0,
		f.Api.Add(f.Api.Mul(exponent, mantissa_low), mantissa))
	// This number has LOGN + ES + mantissa_bit_length - 1 bits, and we want to round to LOGN + efbits bits.
	// So, we shift left by efbits and then round based on the last ES + mantissa_bit_length - 1 bits
	// decompose combined_e_m = p || q || r || s
	q_idx := f.ES + mantissa_bit_length - 1
	q_shift := new(big.Int).Lsh(big.NewInt(1), q_idx)
	r_shift := new(big.Int).Lsh(big.NewInt(1), q_idx - 1)
	outputs, err = f.Api.Compiler().NewHint(hint.DecomposeMantissaForRoundingHint, 4, combined_e_m, 1, f.Api.Add(ebits, fbits), q_idx + 1, q_idx, q_idx - 1)
	if err != nil {
		panic(err)
	}
	p := outputs[0]
	q := outputs[1]
	r := outputs[2]
	s := outputs[3]
	// Make sure q, r are boolean and p, s are small
	f.Gadget.AssertBitLength(p, f.N - 3 + f.LOGN, gadget.Loose)
	f.Api.AssertIsBoolean(q)
	f.Api.AssertIsBoolean(r)
	f.Gadget.AssertBitLength(s, q_idx - 1, gadget.TightForSmallAbs)
	// Make sure p || q || r || s == combined_e_m << efbits
	pq := f.Api.Add(p,p,q)
	rs := f.Api.Add(f.Api.Mul(r, r_shift), s)
	f.Api.AssertIsEqual(
		f.Api.Add(f.Api.Mul(pq, q_shift), rs),
		f.Api.Mul(combined_e_m, efshift))
	// if r == 1 and s == 0, round based on q, otherwise round based on r
	carry := f.Api.Select(f.Gadget.IsEq(rs, r_shift), q, r)
	rounded := f.Api.Add(pq, carry)
	// shift left by ES + M - 1 - efbits
	rounded = f.Api.Div(f.Api.Mul(rounded, f.MAX_E, new(big.Int).Lsh(big.NewInt(1), f.M)), efshift)
	// re-extract exponent and mantissa
	outputs, err = f.Api.Compiler().NewHint(hint.TruncHint, 1, rounded, f.M)
	if err != nil {
		panic(err)
	}
	re := outputs[0]
	mantissa = f.Api.Sub(rounded, f.Api.Mul(re, new(big.Int).Lsh(big.NewInt(1), f.M)))
	outputs, err = f.Api.Compiler().NewHint(hint.TruncHint, 1, re, f.ES)
	if err != nil {
		panic(err)
	}
	regime = outputs[0]
	e = f.Api.Sub(re, f.Api.Mul(regime, f.MAX_E))
	// Make sure regime, e, and mantissa are small
	f.Gadget.AssertBitLength(regime, f.LOGN, gadget.Loose)
	f.Gadget.AssertBitLength(e, f.ES, gadget.TightForSmallAbs)
	f.Gadget.AssertBitLength(mantissa, f.M, gadget.TightForSmallAbs)

	return f.Api.Add(f.Api.Select(zero_mantissa, 0, new(big.Int).Lsh(big.NewInt(1), f.M)), mantissa), regime, e
}

// Add two numbers.
func (f *Context) Add(x, y PositVar) PositVar {
	f.Api.Compiler().MarkBoolean(x.Sign)
	f.Api.Compiler().MarkBoolean(y.Sign)
	// We can basically treat this as float addition where the exponent is MAX_E*r + e
	xre := f.Api.Add(f.Api.Mul(f.MAX_E, f.Api.Sub(x.Regime, f.N-1)), x.Exponent)
	yre := f.Api.Add(f.Api.Mul(f.MAX_E, f.Api.Sub(y.Regime, f.N-1)), y.Exponent)

	// Compute `y.exponent - x.exponent`'s absolute value and sign.
	// Since `delta` is the absolute value, `delta >= 0`.
	delta := f.Api.Sub(yre, xre)
	delta, ex_le_ey := f.Gadget.Abs(delta, f.LOGN + f.ES)

	// The exponent of the result is at most `max(x.exponent, y.exponent) + 1`, where 1 is the possible carry.
	exponent := f.Api.Add(
		f.Api.Select(
			ex_le_ey,
			yre,
			xre,
		),
		1,
	)

	// Then we are going to use `delta` to align the mantissas of `x` and `y`.
	// If `delta` is 0, we don't need to shift the mantissas.
	// Otherwise, we need to shift the mantissa of the number with smaller exponent to the right by `delta` bits.
	// Now we check if `delta >= M + 2`, i.e., if the difference is too large.
	// If so, the mantissa of the number with smaller exponent will be completely shifted out, and hence the
	// effect of shifting by `delta` bits is the same as shifting by `M + 2` bits.
	// Therefore, the actual right shift count is `min(delta, M + 2)`.
	// As discussed in `Self::round`, we can shift left by `M + 2 - min(delta, M + 2) = max(M + 2 - delta, 0)`
	// bits instead of shifting right by `min(delta, M + 2)` bits in order to save constraints.
	delta = f.Gadget.Max(
		f.Api.Sub(f.M+2, delta),
		0,
		f.LOGN + f.ES,
	)
	// Enforce that `two_to_delta` is equal to `2^delta`, where `delta` is known to be small.
	two_to_delta := f.Gadget.QueryPowerOf2(delta)

	// Compute the signed mantissas
	xx := f.Api.Select(
		x.Sign,
		f.Api.Neg(x.Mantissa),
		x.Mantissa,
	)
	yy := f.Api.Select(
		y.Sign,
		f.Api.Neg(y.Mantissa),
		y.Mantissa,
	)
	// `zz` is the mantissa of the number with smaller exponent, and `ww` is the mantissa of another number.
	zz := f.Api.Select(
		ex_le_ey,
		xx,
		yy,
	)
	ww := f.Api.Sub(f.Api.Add(xx, yy), zz)

	// Align `zz` and `ww`.
	// Naively, we can shift `zz` to the right by `delta` bits and keep `ww` unchanged.
	// However, as mentioned above, we left shift `zz` by `M + 2 - min(delta, M + 2)` bits and `ww` by `M + 2`
	// bits instead for circuit efficiency.
	// Also, note that if `exponent` is subnormal and w.l.o.g. `x.exponent < y.exponent`, then `zz` has
	// `E_NORMAL_MIN - x.exponent` trailing 0s, and `ww` has `E_NORMAL_MIN - y.exponent` trailing 0s.
	// Hence, `zz * 2^delta` has `E_NORMAL_MIN - x.exponent + M + 2 - y.exponent + x.exponent` trailing 0s,
	// and `ww << (M + 2)` has `E_NORMAL_MIN - y.exponent + M + 2` trailing 0s.
	// This implies that `s` also has `E_NORMAL_MIN - y.exponent + M + 2` trailing 0s.
	// Generally, `s` should have `max(E_NORMAL_MIN - max(x.exponent, y.exponent), 0) + M + 2` trailing 0s.
	s := f.Api.Add(f.Api.Mul(zz, two_to_delta), f.Api.Mul(ww, new(big.Int).Lsh(big.NewInt(1), f.M+2)))

	// The shift count is at most `M + 2`, and both `zz` and `ww` have `M + 1` bits, hence the result has at most
	// `(M + 2) + (M + 1) + 1` bits, where 1 is the possible carry.
	mantissa_bit_length := (f.M + 2) + (f.M + 1) + 1

	// Get the sign of the mantissa and find how many bits to shift the mantissa to the left to have the
	// `mantissa_bit_length - 1`-th bit equal to 1.
	// Prodive these values as hints to the circuit
	outputs, err := f.Api.Compiler().NewHint(hint.AbsHint, 2, s)
	if err != nil {
		panic(err)
	}
	mantissa_ge_0 := outputs[0]
	mantissa_abs := outputs[1]
	f.Api.AssertIsBoolean(mantissa_ge_0)
	mantissa_lt_0 := f.Api.Sub(1, mantissa_ge_0)
	f.Api.Compiler().MarkBoolean(mantissa_lt_0)
	outputs, err = f.Api.Compiler().NewHint(hint.NormalizeHint, 1, mantissa_abs, big.NewInt(int64(mantissa_bit_length)))
	if err != nil {
		panic(err)
	}
	shift := outputs[0]
	// Enforce that `shift` is small and `two_to_shift` is equal to `2^shift`.
	// Theoretically, `shift` should be in the range `[0, M + 4]`, but the circuit can only guarantee
	// that `shift` is in the range `[0, M + E]`.
	// However, we will check the range of `|s| * two_to_shift` later, which will implicitly provide
	// tight upper bounds for `shift` and `two_to_shift`, and thus soundness still holds.
	f.Gadget.AssertBitLength(shift, uint(big.NewInt(int64(mantissa_bit_length)).BitLen()), gadget.Loose)
	two_to_shift := f.Gadget.QueryPowerOf2(shift)

	// Compute the shifted absolute value of mantissa
	mantissa := f.Api.Mul(
		f.Api.Select(
			mantissa_ge_0,
			s,
			f.Api.Neg(s),
		),
		two_to_shift,
	)

	mantissa_is_zero := f.Api.IsZero(mantissa)
	mantissa_is_not_zero := f.Api.Sub(1, mantissa_is_zero)
	f.Api.Compiler().MarkBoolean(mantissa_is_not_zero)

	// Enforce that the MSB of the shifted absolute value of mantissa is 1 unless the mantissa is zero.
	// Soundness holds because
	// * `mantissa` is non-negative. Otherwise, `mantissa - !mantissa_is_zero << (mantissa_bit_length - 1)`
	// will be negative and cannot fit in `mantissa_bit_length - 1` bits.
	// * `mantissa` has at most `mantissa_bit_length` bits. Otherwise,
	// `mantissa - !mantissa_is_zero << (mantissa_bit_length - 1)` will be greater than or equal to
	// `2^(mantissa_bit_length - 1)` and cannot fit in `mantissa_bit_length - 1` bits.
	// * `mantissa`'s MSB is 1 unless `mantissa_is_zero`. Otherwise, `mantissa - 1 << (mantissa_bit_length - 1)`
	// will be negative and cannot fit in `mantissa_bit_length - 1` bits.
	mantissa_msb := f.Api.Mul(mantissa_is_not_zero, new(big.Int).Lsh(big.NewInt(1), mantissa_bit_length-1))
	mantissa_no_msb := f.Api.Sub(mantissa, mantissa_msb)
	f.Gadget.AssertBitLength(
		mantissa_no_msb,
		mantissa_bit_length-1,
		gadget.TightForSmallAbs,
	)
	// Decrement the exponent by `shift`.
	exponent = f.Api.Sub(exponent, shift)

	// Re-bias the regime by adding (N-1) * 2^ES
	exponent = f.Api.Add(exponent, (f.N-1) << f.ES)

	is_infinity := f.Api.Or(
		f.Api.And(f.Api.IsZero(x.Regime), x.Sign),
		f.Api.And(f.Api.IsZero(y.Regime), y.Sign),
	)

	mantissa_shifted, regime, e := f.round(mantissa_no_msb, f.Api.Or(is_infinity, mantissa_is_zero), mantissa_bit_length, exponent)

	return PositVar{
		Sign:     f.Api.Select(is_infinity, 1, mantissa_lt_0),
		Regime:   regime,
		Exponent: e,
		Mantissa: mantissa_shifted,
	}
}

// Compute the absolute value of the number.
func (f *Context) Abs(x PositVar) PositVar {
	return PositVar{
		Sign:       f.Api.Select(f.Api.IsZero(x.Regime), x.Sign, 0),
		Regime:     x.Regime,
		Exponent:   x.Exponent,
		Mantissa:   x.Mantissa,
	}
}

// Negate the number by flipping the sign.
func (f *Context) Neg(x PositVar) PositVar {
	neg_sign := f.Api.Sub(1, x.Sign)
	f.Api.Compiler().MarkBoolean(neg_sign)
	return PositVar{
		Sign:       f.Api.Select(f.Api.IsZero(x.Regime), x.Sign, neg_sign),
		Regime:     x.Regime,
		Exponent:   x.Exponent,
		Mantissa:   x.Mantissa,
	}
}

// Subtract two numbers.
// This is implemented by negating `y` and adding it to `x`.
func (f *Context) Sub(x, y PositVar) PositVar {
	return f.Add(x, f.Neg(y))
}

// Multiply two numbers.
func (f *Context) Mul(x, y PositVar) PositVar {
	// If either number is 0 or infinite, we copy that sign.
	// Otherwise, the result is negative if and only if the signs of x and y are different.
	xr_zero := f.Api.IsZero(x.Regime)
	yr_zero := f.Api.IsZero(y.Regime)
	sign := f.Api.Lookup2(xr_zero, yr_zero, f.Api.Xor(x.Sign, y.Sign), x.Sign, y.Sign, f.Api.Or(x.Sign, y.Sign))

	mantissa := f.Api.Mul(x.Mantissa, y.Mantissa)
	// Since both `x.mantissa` and `y.mantissa` are in the range [2^M, 2^(M + 1)), the product is
	// in the range [2^(2M), 2^(2M + 2)) and requires 2M + 2 bits to represent.
	mantissa_bit_length := (f.M + 1) * 2

	// Get the MSB of the mantissa and provide it as a hint to the circuit.
	outputs, err := f.Api.Compiler().NewHint(hint.NthBitHint, 1, mantissa, big.NewInt(int64(mantissa_bit_length-1)))
	if err != nil {
		panic(err)
	}
	mantissa_msb := outputs[0]
	f.Api.AssertIsBoolean(mantissa_msb)
	// Enforce that `mantissa_msb` is indeed the MSB of the mantissa.
	// Soundness holds because
	// * If `mantissa_msb == 0` but the actual MSB is 1, then the subtraction result will have at least
	// mantissa_bit_length bits.
	// * If `mantissa_msb == 1` but the actual MSB is 0, then the subtraction will underflow to a negative
	// value.
	f.Gadget.AssertBitLength(
		f.Api.Sub(mantissa, f.Api.Mul(mantissa_msb, new(big.Int).Lsh(big.NewInt(1), mantissa_bit_length-1))),
		mantissa_bit_length-1,
		gadget.TightForSmallAbs,
	)
	// Shift the mantissa to the left to make the MSB 1.
	// Since `mantissa` is in the range `[2^(2M), 2^(2M + 2))`, either the MSB is 1 or the second MSB is 1.
	// Therefore, we can simply double the mantissa if the MSB is 0.
	mantissa = f.Api.Add(
		mantissa,
		f.Api.Select(
			mantissa_msb,
			0,
			mantissa,
		),
	)

	// Compute the exponent of the result. We should increment the exponent if the multiplication
	// carries, i.e., if the MSB of the mantissa is 1.
	regime_new := f.Api.Sub(f.Api.Add(x.Regime, y.Regime), f.N-1)
	valid_regime := f.Gadget.IsPositive(f.Api.Sub(regime_new, 1), f.LOGN + 1)
	huge_regime := f.Gadget.IsPositive(f.Api.Sub(regime_new, f.ONES_REGIME), f.LOGN + 1)

	exponent := f.Api.Add(f.Api.Mul(f.MAX_E, regime_new), x.Exponent, y.Exponent, mantissa_msb)

	// if exponent < f.MAX_E, fix it
	exponent = f.Api.Select(valid_regime, exponent, f.MAX_E)
	// if exponent is too large, fix it
	exponent = f.Api.Select(huge_regime, f.Api.Mul(f.ONES_REGIME, f.MAX_E), exponent)

	zero_mantissa := f.Api.Or(xr_zero, yr_zero)
	mantissa_no_msb := f.Api.Sub(mantissa, new(big.Int).Lsh(big.NewInt(1), mantissa_bit_length - 1))

	mantissa, regime, e := f.round(
		mantissa_no_msb,
		zero_mantissa,
		mantissa_bit_length,
		exponent,
	)

	return PositVar{
		Sign:     sign,
		Regime:   regime,
		Exponent: e,
		Mantissa: mantissa,
	}
}

func (f *Context) less(x, y PositVar, allow_eq uint) frontend.Variable {
	m := new(big.Int).Lsh(big.NewInt(1), f.M)
	xv := f.Api.Add(f.Api.Mul(f.Api.Add(f.Api.Mul(x.Regime, f.MAX_E), x.Exponent), m), x.Mantissa)
	yv := f.Api.Add(f.Api.Mul(f.Api.Add(f.Api.Mul(x.Regime, f.MAX_E), x.Exponent), m), y.Mantissa)
	xv_lt_yv := f.Api.Sub(1, f.Gadget.IsPositive(f.Api.Sub(xv, yv), f.LOGN + f.ES + f.M))
	f.Api.Compiler().MarkBoolean(xv_lt_yv)

	x_pos := f.Api.Sub(1, x.Sign)
	f.Api.Compiler().MarkBoolean(x_pos)
	b := f.Api.Or(
		f.Api.And(x_pos, y.Sign), // x positive, y negative
		f.Api.Xor(
			x.Sign,
			f.Api.Or(
				xv_lt_yv, // x < y
				f.Api.And(
					f.Gadget.IsEq(xv, yv),
						f.Api.Xor(
							1 - allow_eq,
							x.Sign,
						),
					))),
	)
	f.Api.Compiler().MarkBoolean(b)
	return b
}

func (f *Context) IsLt(x, y PositVar) frontend.Variable {
	return f.less(x, y, 0)
}

func (f *Context) IsLe(x, y PositVar) frontend.Variable {
	return f.less(x, y, 1)
}

func (f *Context) IsGt(x, y PositVar) frontend.Variable {
	return f.less(y, x, 0)
}

func (f *Context) IsGe(x, y PositVar) frontend.Variable {
	return f.less(y, x, 1)
}

func (f *Context) Trunc(x PositVar) PositVar {
	e_ge_0 := f.Gadget.IsPositive(f.Api.Sub(x.Regime, f.N-1), f.N)
	xre := f.Api.Select(
		e_ge_0,
		f.Api.Add(f.Api.Mul(f.MAX_E, f.Api.Sub(x.Regime, f.N-1)), x.Exponent),
		big.NewInt(-1),
	)
	two_to_e := f.Gadget.QueryPowerOf2(f.Gadget.Max(
		f.Api.Sub(f.M, xre),
		0,
		f.LOGN + f.ES + 1,
	))
	// Instead of computing `x.Mantissa >> e` directly, we compute `(x.Mantissa << (M + 1)) >> e` first and
	// decompose it later to save constraints.
	m := f.Api.DivUnchecked(f.Api.Mul(x.Mantissa, new(big.Int).Lsh(big.NewInt(1), f.M+1)), two_to_e)
	outputs, err := f.Api.Compiler().NewHint(hint.TruncHint, 1, m, f.M+1)
	if err != nil {
		panic(err)
	}
	q := outputs[0]
	r := f.Api.Sub(m, f.Api.Mul(q, new(big.Int).Lsh(big.NewInt(1), f.M+1)))
	// Enforce `q` to be small
	f.Gadget.AssertBitLength(q, f.M+1, gadget.Loose)
	// Enforce that `0 <= r < 2^(M + 1)`, where `2^(M + 1)` is the divisor.
	f.Gadget.AssertBitLength(r, f.M+1, gadget.TightForSmallAbs)

	return PositVar{
		Sign:       f.Api.Select(f.Api.Or(e_ge_0, f.Api.IsZero(x.Regime)), x.Sign, 0),
		Regime:     f.Api.Select(e_ge_0, x.Regime, 0),
		Exponent:   f.Api.Select(e_ge_0, x.Exponent, 0),
		Mantissa:   f.Api.Mul(q, two_to_e),
	}
}

func (f *Context) Floor(x PositVar) PositVar {
	e_ge_0 := f.Gadget.IsPositive(f.Api.Sub(x.Regime, f.N-1), f.LOGN)
	xre := f.Api.Select(
		e_ge_0,
		f.Api.Add(f.Api.Mul(f.MAX_E, f.Api.Sub(x.Regime, f.N-1)), x.Exponent),
		big.NewInt(-1),
	)
	two_to_e := f.Gadget.QueryPowerOf2(f.Gadget.Max(
		f.Api.Sub(f.M, xre),
		0,
		f.LOGN + f.ES + 1,
	))
	// Instead of computing `x.Mantissa >> e` directly, we compute `(x.Mantissa << (M + 1)) >> e` first and
	// decompose it later to save constraints.
	m := f.Api.DivUnchecked(f.Api.Mul(x.Mantissa, new(big.Int).Lsh(big.NewInt(1), f.M+1)), two_to_e)
	outputs, err := f.Api.Compiler().NewHint(hint.FloorHint, 1, m, f.M+1, x.Sign)
	if err != nil {
		panic(err)
	}
	// If `x` is positive, then `q` is the floor of `m / 2^(M + 1)`, and the remainder `r` is positive.
	// Otherwise, `q` is the ceiling of `m / 2^(M + 1)`, and the remainder `r` is negative.
	q := outputs[0]
	r := f.Api.Sub(m, f.Api.Mul(q, new(big.Int).Lsh(big.NewInt(1), f.M+1)))
	// Enforce `q` to be small
	f.Gadget.AssertBitLength(q, f.M+1, gadget.Loose)
	// Enforce that `0 <= |r| < 2^(M + 1)`, where `2^(M + 1)` is the divisor.
	f.Gadget.AssertBitLength(f.Api.Select(x.Sign, f.Api.Neg(r), r), f.M+1, gadget.TightForSmallAbs)

	mantissa := f.Api.Mul(q, two_to_e)
	// `mantissa` may overflow when `x` is negative, so we need to fix it.
	ebits, _, _, fshift := f.efbits(x.Regime)
	mantissa_overflow := f.Gadget.IsEq(mantissa, f.Api.Mul(2, fshift))
	next_exponent := f.Api.And(mantissa_overflow, f.Gadget.IsEq(ebits, f.ES))
	exponent_overflow := f.Gadget.IsEq(f.Api.Add(x.Exponent, next_exponent), f.MAX_E)
	is_max_regime := f.Gadget.IsEq(x.Regime, f.ONES_REGIME)
	next_exponent = f.Api.And(next_exponent, f.Api.Sub(1, f.Api.And(exponent_overflow, is_max_regime)))
	next_regime := f.Api.And(exponent_overflow, f.Api.Sub(1, is_max_regime))

	shift_back := f.Api.DivUnchecked(new(big.Int).Lsh(big.NewInt(1), f.M), fshift)
	mantissa = f.Api.Select(
		mantissa_overflow,
		f.Api.Select(
			next_exponent,
			new(big.Int).Lsh(big.NewInt(1), f.M),
			f.Api.Sub(new(big.Int).Lsh(big.NewInt(1), f.M+1), shift_back)),
		mantissa)

	xre = f.Api.Add(xre, mantissa_overflow)

	return PositVar{
		Sign:       f.Api.Select(f.Api.Or(e_ge_0, f.Api.IsZero(x.Regime)), x.Sign, 0),
		Regime:     f.Api.Select(e_ge_0, f.Api.Add(x.Regime, next_regime), 0),
		Exponent:   f.Api.Select(e_ge_0, f.Api.Add(x.Exponent, next_exponent), 0),
		Mantissa:   mantissa,
	}
}

func (f *Context) Ceil(x PositVar) PositVar {
	return f.Neg(f.Floor(f.Neg(x)))
}

// Convert a float to an integer (f64 to i64, f32 to i32).
// A negative integer will be represented as `r - |x|`, where `r` is the order of the native field.
// The caller should ensure that `x` is obtained from `Trunc`, `Floor` or `Ceil`.
// Also, `x`'s exponent should not be too large. Otherwise, the proof verification will fail.
func (f *Context) ToInt(x PositVar) frontend.Variable {
	expt := f.Api.Add(f.Api.Mul(f.MAX_E, f.Api.Sub(x.Regime, f.N-1)), x.Exponent)
	expt_capped := f.Gadget.Max(f.Gadget.Min(expt, 64, f.N + f.ES + 1), 0, f.N + f.ES + 1)
	two_to_e := f.Gadget.QueryPowerOf2(expt_capped)
	v := f.Api.Div(f.Api.Mul(x.Mantissa, two_to_e), new(big.Int).Lsh(big.NewInt(1), f.M))
	return f.Api.Select(
		x.Sign,
		f.Api.Neg(v),
		v,
	)
}

func (f *Context) Select(c frontend.Variable, x, y PositVar) PositVar {
	return PositVar{
		Sign:       f.Api.Select(c, x.Sign, y.Sign),
		Regime:     f.Api.Select(c, x.Regime, y.Regime),
		Exponent:   f.Api.Select(c, x.Exponent, y.Exponent),
		Mantissa:   f.Api.Select(c, x.Mantissa, y.Mantissa),
	}
}
