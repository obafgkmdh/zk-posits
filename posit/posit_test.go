package posit

import (
	"bufio"
	"fmt"
	"testing"
	"math/big"
	"os"
	"path/filepath"
	"reflect"
	"strings"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/test"
)

type P32BinaryCircuit struct {
	X  frontend.Variable `gnark:",secret"`
	Y  frontend.Variable `gnark:",secret"`
	Z  frontend.Variable `gnark:",public"`
	op string
}

func (c *P32BinaryCircuit) Define(api frontend.API) error {
	ctx := NewContext(api, 0, 32, 3)
	x := ctx.NewPosit(c.X)
	y := ctx.NewPosit(c.Y)
	z := ctx.NewPosit(c.Z)
	ctx.AssertIsEqual(reflect.ValueOf(&ctx).MethodByName(c.op).Call([]reflect.Value{reflect.ValueOf(x), reflect.ValueOf(y)})[0].Interface().(PositVar), z)
	return nil
}

type P32ConversionCircuit struct {
	X  frontend.Variable `gnark:",secret"`
	Y  frontend.Variable `gnark:",public"`
	op string
}

func (c *P32ConversionCircuit) Define(api frontend.API) error {
	ctx := NewContext(api, 0, 32, 3)
	x := ctx.NewPosit(c.X)
	x = reflect.ValueOf(&ctx).MethodByName(c.op).Call([]reflect.Value{reflect.ValueOf(x)})[0].Interface().(PositVar)
	api.AssertIsEqual(ctx.ToInt(x), c.Y)
	return nil
}

func TestP32ConversionCircuit(t *testing.T) {
	assert := test.NewAssert(t)

	assert.ProverSucceeded(
		&P32ConversionCircuit{X: 0, Y: 0, op: "Floor"},
		&P32ConversionCircuit{X: 0b0_10_110_011001_11001000000000000000, Y: int32(89), op: "Floor"},
		test.WithCurves(ecc.BN254),
		test.WithBackends(backend.GROTH16, backend.PLONK),
	)

	assert.ProverSucceeded(
		&P32ConversionCircuit{X: 0, Y: 0, op: "Ceil"},
		&P32ConversionCircuit{X: 0b0_10_110_011001_11001000000000000000, Y: int32(90), op: "Ceil"},
		test.WithCurves(ecc.BN254),
		test.WithBackends(backend.GROTH16, backend.PLONK),
	)

	assert.ProverSucceeded(
		&P32ConversionCircuit{X: 0, Y: 0, op: "Trunc"},
		&P32ConversionCircuit{X: 0b1_01_001_100110_11001000000000000000, Y: -int32(89), op: "Trunc"},
		test.WithCurves(ecc.BN254),
		test.WithBackends(backend.GROTH16, backend.PLONK),
	)

	assert.ProverSucceeded(
		&P32ConversionCircuit{X: 0, Y: 0, op: "Ceil"},
		&P32ConversionCircuit{X: 0b0_01_111_111111_11001000000000000000, Y: int32(1), op: "Ceil"},
		test.WithCurves(ecc.BN254),
		test.WithBackends(backend.GROTH16, backend.PLONK),
	)

	assert.ProverSucceeded(
		&P32ConversionCircuit{X: 0, Y: 0, op: "Ceil"},
		&P32ConversionCircuit{X: 0b0_00_000_000000_00000000000000000000, Y: int32(0), op: "Ceil"},
		test.WithCurves(ecc.BN254),
		test.WithBackends(backend.GROTH16, backend.PLONK),
	)

	assert.ProverSucceeded(
		&P32ConversionCircuit{X: 0, Y: 0, op: "Trunc"},
		&P32ConversionCircuit{X: 0b0_10_000_000000_00000000000000000000, Y: int32(1), op: "Trunc"},
		test.WithCurves(ecc.BN254),
		test.WithBackends(backend.GROTH16, backend.PLONK),
	)
}

func TestP32BinaryCircuit(t *testing.T) {
	assert := test.NewAssert(t)

	ops := []string{"Add", "Sub", "Mul"}

	for _, op := range ops {
		path, _ := filepath.Abs(fmt.Sprintf("../data/p32/%s", strings.ToLower(op)))
		file, _ := os.Open(path)
		defer file.Close()

		scanner := bufio.NewScanner(file)
		for scanner.Scan() {
			data := strings.Fields(scanner.Text())
			a, _ := new(big.Int).SetString(data[0], 16)
			b, _ := new(big.Int).SetString(data[1], 16)
			c, _ := new(big.Int).SetString(data[2], 16)

			assert.ProverSucceeded(
				&P32BinaryCircuit{X: 0, Y: 0, Z: 0, op: op},
				&P32BinaryCircuit{X: a, Y: b, Z: c, op: op},
				test.WithCurves(ecc.BN254),
				test.WithBackends(backend.GROTH16, backend.PLONK),
			)
		}
	}
}
