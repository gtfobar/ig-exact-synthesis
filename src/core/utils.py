import logging
import sys
import os
from itertools import islice
from mig import MIG

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


def not_inclusive_range(start, end):
    return range(start + 1, end)

def reverse_readline(filename, buf_size=8192):
    """A generator that returns the lines of a file in reverse order"""
    with open(filename) as fh:
        segment = None
        offset = 0
        fh.seek(0, os.SEEK_END)
        file_size = remaining_size = fh.tell()
        while remaining_size > 0:
            offset = min(file_size, offset + buf_size)
            fh.seek(file_size - offset)
            buffer = fh.read(min(remaining_size, buf_size))
            remaining_size -= buf_size
            lines = buffer.split('\n')
            # The first line of the buffer is probably not a complete line so
            # we'll save it and append it to the last line of the next buffer
            # we read
            if segment is not None:
                # If the previous chunk starts right from the beginning of line
                # do not concat the segment to the last line of new chunk.
                # Instead, yield the segment first 
                if buffer[-1] != '\n':
                    lines[-1] += segment
                else:
                    yield segment
            segment = lines[0]
            for index in range(len(lines) - 1, 0, -1):
                if lines[index]:
                    yield lines[index]
        # Don't yield None if the file was empty
        if segment is not None:
            yield segment

def get_latest_function_synthesized(filename):
    try:
        
        line_gen = reverse_readline(filename)
        line = ""
        while 'mig' != line:
            line = next(line_gen)
        code = int(next(line_gen))
        return code
    except Exception as e:
        print(f'File parsing error: {e}')
        return -1

# +
def swap_vars(f, x, y, n):
    visited = set()
    for i in range(0, 1 << n):
        if i in visited:
            continue
        visited.add(i)
        var_values = int2bitvec(n, i)
        if var_values[x] == var_values[y]:
            continue
        var_values[x], var_values[y] = var_values[y], var_values[x]
        j = bitvec2int(var_values)
        f[i], f[j] = f[j], f[i]
        visited.add(j)
# +
def get_permuted(f, permutation, n):
    permuted = f[:]
    for i, j in enumerate(permutation):
        if i == j:
            continue
        swap_vars(permuted, i, j, n)
        idx = permutation.index(i)
        permutation[i], permutation[idx] = permutation[idx], permutation[i]
    return permuted


# invert k-th variable of func f
def invert_var(f, k, n):
    visited = set()
    for i in range(0, 1 << n):
        if i in visited:
            continue
        visited.add(i)
        var_values = int2bitvec(n, i)
        var_values[k] = 1 - var_values[k] # invert k-th var
        j = bitvec2int(var_values)
        f[i], f[j] = f[j], f[i]
        visited.add(j)

def get_inverted(f, combination, n):
    inverted = f[:]
    for i, value in enumerate(combination):
        if value == 0:
            continue
        invert_var(inverted, i, n)
    return inverted

def get_permutations(n):
    result = [[]]
    for k in range(0, n):
        done = result
        result = []
        for permutation in done:
            for i in range(0, k + 1):
                tmp = permutation[:]
                tmp.insert(i, k)
                result.append(tmp)
    return result

def get_combinations(n):
    result = [[]]
    for k in range(0, n):
        done = result
        result = []
        for combination in done:
            for i in {0, 1}:
                tmp = combination[:]
                tmp += [i]
                result.append(tmp)
    return result

def get_mincode(code, n=5):
    # print(f"Hello from {mps.current_process()}")
    permutations = get_permutations(n)
    combinations = get_combinations(n)
    mincode = 2 ** 32
    f = int2bitvec(2 ** n, code)
    for permutation in permutations:
        permuted = get_permuted(f, permutation, n)
        for combination in combinations:
            inverted = get_inverted(permuted, combination, n)
            mincode = min(mincode, bitvec2int(inverted))
    return mincode

def write_string(string, filename, mode):
    if string == '':
        logging.info(f'Attempt to write empty string to {filename}\n')
        return

    if filename is None:
        logging.info(f'Filename is None, writing to stdout:\n{string}\n')
        sys.stdout.write(string)
        return

    with open(filename, mode) as file:
        logging.info(f'Writing to {filename}:\n{string}\n')
        file.write(string)

def write_string_rewrite(string, filename):
    write_string(string, filename, 'w+')

def write_string_append(string, filename):
    write_string(string, filename, 'a+')

def get_int_arg(key, args, default):
    value = vars(args)[key]
    arg = default if value is None else int(value)
    return arg

def mks1_parse_mig(filename):
    migs = []
    with open(filename, 'r') as f:
        while True:
            try:
                mig_str = ''.join(list(islice(f, 5)))
                migs.append(MIG(mig_str))
            except:
                break
            
    return migs