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

import os

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
        while 'mig' != line and not line is None:
            line = reverse_readline(filename)
        code = int(reverse_readline(filename))
        return code
    except Exception as e:
        return -1
