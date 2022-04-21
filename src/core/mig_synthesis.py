import time
import argparse
import sys
import logging
from bool_function import BoolFunction
from z3_model_wrapper import Z3ModelWrapper
from utils import (
    get_latest_function_synthesized,
    write_string_rewrite,
    write_string_append
)

logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)
MAX_COMPLEXITY = 10

def init_argparse():
    parser = argparse.ArgumentParser(description='Exact synthesis of MIG.')
    parser.add_argument('-o', '--output', help='Write results to file.')
    parser.add_argument('-i', '--input', help='Read function codes from file.')
    parser.add_argument('-c', '--check', help='Check complexity.', type=int)
    parser.add_argument('-d', '--dir', help='Write results to directory, separate file for each function.')
    parser.add_argument('-m', '--max-complexity', help='Maximum complexity.', type=int) # todo
    parser.add_argument('function_codes', metavar='f1, f2, f3', nargs='*', help='Function codes.', type=int)

    args = parser.parse_args()
    return args

def synthesize_mig(code, max_complexity=MAX_COMPLEXITY):
    f = BoolFunction(code, 5)
    gate = BoolFunction(BoolFunction.MAJ_CODE, 3)

    m = None

    for complexity in range(max_complexity + 1):
        m = Z3ModelWrapper(complexity, f, gate)

        start = time.time()
        logging.info(f'checking {complexity}...')
        check_result = m.check()
        elapsed = time.time() - start

        if check_result is None:
            logging.info(f'[Time elapsed: {elapsed}] error\n')
            return m
        elif check_result:
            logging.info(f'[Time elapsed: {elapsed}] ***** sat *****\n')
            return m
        logging.info('[Time elapsed: {elapsed}] unsat')
    return m

def check_complexity(code, complexity):
    f = BoolFunction(code, 5)
    gate = BoolFunction(BoolFunction.MAJ_CODE, 3)

    m = Z3ModelWrapper(complexity, f, gate)

    start = time.time()
    logging.info(f'checking {complexity}...')
    check_result = m.check()
    elapsed = time.time() - start

    if check_result is None:
        logging.info('error')
    elif check_result:
        logging.info('***** sat *****\n')
    else:
        logging.info('unsat')
    
    logging.info(f'Time elapsed: {elapsed}')

    return m

def get_function_codes(args):
    max_function_code = 0x1000
    function_codes = []

    if args.input is not None:
        with open(args.input, 'r') as inputt:
            function_codes += map(int, inputt.read().split())

    if args.function_codes is not None:
        function_codes += args.function_codes

    if not function_codes:
        latest_code = get_latest_function_synthesized(args.output)
        function_codes = range(latest_code + 1, max_function_code)

    logging.info(function_codes)
    
    return function_codes

def to_dir(function_codes, args):
    write_string_append(f'{sys.argv}\n', f'{args.dir}/meta')
    for code in function_codes:
        logging.info(f'\n***** Function {code} *****')
        if args.check is None:
            m = synthesize_mig(code, MAX_COMPLEXITY)
        else:
            m = check_complexity(code, args.check)
        write_string_rewrite(str(m), f'{args.dir}/{code}')

def to_file(function_codes, args):
    for code in function_codes:
        logging.info(f'\n***** Function {code} *****')
        if args.check is None:
            m = synthesize_mig(code, MAX_COMPLEXITY)
        else:
            m = check_complexity(code, args.check)
        write_string_append(str(m), args.output)

def main():
    args = init_argparse()
    function_codes = get_function_codes(args)

    global MAX_COMPLEXITY
    if args.max_complexity is not None:
        MAX_COMPLEXITY = args.max_complexity

    if args.dir is not None:
        to_dir(function_codes, args)
        return

    to_file(function_codes, args)
    
if __name__ == "__main__":
    main()
