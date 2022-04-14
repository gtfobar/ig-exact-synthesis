## Useful stuff from intel_altera
def vector_to_int(vector):
    result = 0
    for i, x in enumerate(vector):
        result += x * (2 ** i)
    return result


def int_to_vector(x, vector_dim):
    result = []
    for _ in range(vector_dim):
        result.append(x & 1)
        x >>= 1
    return result

## Important cell do not remove

def bool2int(x: bool) -> int:
    return x # 1 if x else 0


def bitvec2int(bitvec):
    result = 0
    bitvec.reverse()
    for i, xi in enumerate(bitvec):
        result += xi * (2 ** i)
    return result


def int2bitvec(n, i):
    result = []
    for _ in range(n):
        result.append(i & 1)
        i >>= 1
    result.reverse()
    return result


"""
f - битовый вектор длины 2 ** n
x - битовый вектор длины n
"""
def evaluate_fun(f, x):
    n = len(x)
    if (len(f) != 2 ** n):
        raise Exception("Bad arguments")
    x = bitvec2int(x)
    return f[x]


def right_inclusive_range(start, end):
    return range(start + 1, end + 1)