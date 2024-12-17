from sgposit.pcposit import PCPosit
from sgposit.coder import encode_posit_binary
try: from tqdm import tqdm
except ImportError: tqdm = lambda x, **kwargs: x
import random, itertools

BINARY_OPS = ["add", "sub", "mul", "div"]

def gen_tests(op, size, es, seed=0, n=10):
	posits = [
		PCPosit(1, mode='bits', nbits=size, es=es), # smallest positive posit
		PCPosit((1 << (size-1)) - 1, mode='bits', nbits=size, es=es), # largest finite posit
		PCPosit(1 << (size-2), mode='bits', nbits=size, es=es), # 1
		PCPosit((1 << (size-2)) - 1, mode='bits', nbits=size, es=es), # posit before 1
		PCPosit((1 << (size-2)) + 1, mode='bits', nbits=size, es=es), # posit after 1
	]
	for i in range(len(posits)):
		posits.append(-posits[i]) # negatives of the above
	posits.append(PCPosit('0', nbits=size, es=es)) # 0
	posits.append(PCPosit('cinf', nbits=size, es=es)) # inf

	random.seed(seed)

	for i in range(n):
		posits.append(PCPosit(
			random.getrandbits(size),
			mode = 'bits',
			nbits = size,
			es = es
		))

	for x, y in tqdm(itertools.product(posits, repeat=2), total=len(posits)**2):
		result = x.__getattribute__(f"__{op}__")(y)
		yield (x, y, result)

for op in BINARY_OPS:
	with open(f"p32/{op}", "w") as f:
		for triple in gen_tests(op, size=32, es=3, n=20):
			f.write(" ".join(f"{encode_posit_binary(i.rep):04X}" for i in triple) + '\n')

