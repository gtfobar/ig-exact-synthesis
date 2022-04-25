import time
import argparse
import sys
import logging
from bool_function import BoolFunction
from z3_model_wrapper import Z3ModelWrapper
from z3_model_wrapper_optimized import Z3ModelWrapperOptimized
from concurrent.futures import TimeoutError
from pebble import ProcessPool, ProcessExpired
from functools import partial
from utils import (
    get_latest_function_synthesized,
    write_string_rewrite,
    write_string_append,
    get_int_arg,
    mks1_parse_mig
)

DEFAULT_MAX_COMPLEXITY = 10
DEFUALT_COMPLEXITY = 5
DEFAULT_JOBS = 1
DEFAULT_TIMEOUT = None
DEFAULT_OPTIMIZED = 1
DEFAULT_LOG='log/default.log'

def init_argparse():
    parser = argparse.ArgumentParser(description='Exact synthesis of MIG.')
    parser.add_argument('-o', '--output', help='Write results to file.')
    parser.add_argument('-i', '--input', help='Read function codes from file.')
    parser.add_argument('-c', '--check', help='Check complexity.', type=int)
    parser.add_argument('-d', '--dir', help='Write results to directory, separate file for each function.')
    parser.add_argument('-m', '--max-complexity', help=f'Maximum complexity. Default is {DEFAULT_MAX_COMPLEXITY}', type=int)
    parser.add_argument('-j', '--jobs', help=f'Number of concurrent jobs. Default is {DEFAULT_JOBS}', type=int)
    parser.add_argument('-t', '--timeout', help=f'Timeout for single function.', type=int)
    parser.add_argument('-O', '--optimized', help=f'Use optimization technics.', type=int)
    parser.add_argument('function_codes', metavar='f1, f2, f3', nargs='*', help='Function codes.', type=int)
    parser.add_argument('-s', '--sequential', action='store_true', help='Sequential computing. Do not use parallelism')
    parser.add_argument('-I', '--improve',  action='store_true', help=f'Try to improve functions from file')
    parser.add_argument('-l', '--log', help=f'Log file.')

    parser.set_defaults(
        optimized=DEFAULT_OPTIMIZED,
        jobs=DEFAULT_JOBS,
        check=DEFUALT_COMPLEXITY,
        timeout=DEFAULT_TIMEOUT,
        max_complexity=DEFAULT_MAX_COMPLEXITY,
        log=DEFAULT_LOG
        )
    args = parser.parse_args()
    return args

def synthesize_mig(code, args):
    f = BoolFunction(code, 5)
    gate = BoolFunction(BoolFunction.MAJ_CODE, 3)
    # max_complexity = get_int_arg('max_complexity', args, DEFAULT_MAX_COMPLEXITY)
    max_complexity = args.get('max_complexity', DEFAULT_MAX_COMPLEXITY)


    if args['optimized'] == 0:
        z3_model_class = Z3ModelWrapper
    else:
        z3_model_class = Z3ModelWrapperOptimized 

    m = None

    for complexity in range(max_complexity + 1):
        m = z3_model_class(complexity, f, gate)

        start = time.time()
        logging.info(f'{code}:{complexity} checking ...')
        check_result = m.check()
        elapsed = time.time() - start

        if check_result is None:
            logging.info(f'{code}:{complexity}:[Time elapsed: {elapsed}] error\n')
            return m
        elif check_result:
            logging.info(f'{code}:{complexity}:[Time elapsed: {elapsed}] ***** sat *****\n')
            return m
        logging.info(f'{code}:{complexity}:[Time elapsed: {elapsed}] unsat')
    logging.info(f'{code}:Reached maximum complexity of {max_complexity}. Exiting...')
    return m

def check_complexity(code, args):
    f = BoolFunction(code, 5)
    gate = BoolFunction(BoolFunction.MAJ_CODE, 3)

    # complexity = get_int_arg('check', args, DEFUALT_COMPLEXITY)
    complexity = args.get('check', DEFUALT_COMPLEXITY)
  
    if args['optimized'] == 0:
        z3_model_class = Z3ModelWrapper
    else:
        z3_model_class = Z3ModelWrapperOptimized 
    m = z3_model_class(complexity, f, gate)

    start = time.time()
    logging.info(f'{code}:{complexity}: checking ...')
    check_result = m.check()
    elapsed = time.time() - start

    if check_result is None:
        logging.info(f'{code}:error')
    elif check_result:
        logging.info(f'{code}:***** sat *****\n')
    else:
        logging.info(f'{code}:unsat')
    
    logging.info(f'{code}:Time elapsed: {elapsed}')

    return m

def get_function_codes(args):
    max_function_code = 0x1000
    function_codes = []

    if args['input'] is not None:
        with open(args['input'], 'r') as inputt:
            function_codes += map(int, inputt.read().split())

    if args['function_codes'] is not None:
        function_codes += args['function_codes']

    if not function_codes:
        latest_code = get_latest_function_synthesized(args['output'])
        function_codes = range(latest_code + 1, max_function_code)

    logging.info(function_codes)
    
    return function_codes

def compute_single_function(code, args):
    # logging.info(f'\n***** Function {code} *****')
    if args['check'] is None:
        m = synthesize_mig(code, args)
    else:
        m = check_complexity(code, args)
    return m

def write_single_result(result, code, args):
    if args['dir'] is None:
        write_string_append(result.to_mks1(), args['output'])
    else: 
        write_string_rewrite(result.to_mks1(), f'{args["dir"]}/{code}')

def process_single_function(args, code):
    result = compute_single_function(code, args)
    write_single_result(result, code, args)

def compute_in_parallel(function_codes, args):
    if not args['dir'] is None:
        write_string_append(f'{sys.argv}\n', f'{args["dir"]}/meta')
    # jobs = get_int_arg('jobs', args, DEFAULT_JOBS)
    # timeout = get_int_arg('timeout', args, DEFAULT_TIMEOUT)
    jobs = args.get('jobs', DEFAULT_JOBS)
    timeout = args.get('timeout', DEFAULT_TIMEOUT)
    
    logging.info(f'Starting parallel computing with {jobs} jobs, {timeout} timeout')

    with ProcessPool(max_workers=jobs) as pool:
        partial_process_single_function = partial(process_single_function, args)
        future = pool.map(partial_process_single_function, function_codes, timeout=timeout)
        
        iterator = future.result()

        while True:
            try:
                result = next(iterator)
            except StopIteration:
                break
            except TimeoutError as error:
                logging.info("function took longer than %d seconds" % error.args[1])
            except ProcessExpired as error:
                logging.info("%s. Exit code: %d" % (error, error.exitcode))
            except Exception as error:
                logging.info("function raised %s" % error)
                logging.info(error.traceback)  # Python's traceback of remote process
    
        
def improve_single(args, mig):
    if not args['dir'] is None:
        write_string_append(f'{sys.argv}\n', f'{args["dir"]}/meta')
    write_string_rewrite(str(mig.mincode), f'{args["input"]}.meta')
    args['check'] = mig.complexity - 1
    result = check_complexity(mig.mincode, args)
    if result.check_result:
        logging.info(f'MIG complexity for {mig.mincode} IMPROVED! CONGRATULATIONS!')
    write_single_result(result, mig.mincode, args)

def get_migs(args):
    migs = mks1_parse_mig(args['input'])
    try:
        with open(f'{args["input"]}.meta', 'r') as meta:
            improve_checkpoint = int(meta.readline().strip())
    except:
        return migs
    for i, mig in enumerate(migs):
        if mig.mincode == improve_checkpoint:
            migs = migs[i:]
    return migs

def improve_in_parallel(args):
    # jobs = get_int_arg('jobs', args, DEFAULT_JOBS)
    # timeout = get_int_arg('timeout', args, DEFAULT_TIMEOUT)

    jobs = args.get('jobs', DEFAULT_JOBS)
    timeout = args.get('timeout', DEFAULT_TIMEOUT)
    logging.info(f'Starting parallel improvint of  with {jobs} jobs, {timeout} timeout')

    migs = get_migs(args)
    logging.debug(len(migs))

    with ProcessPool(max_workers=jobs) as pool:
        partial_improve_single = partial(improve_single, args)
        future = pool.map(partial_improve_single, migs, timeout=timeout)
        
        iterator = future.result()

        while True:
            try:
                result = next(iterator)
            except StopIteration:
                break
            except TimeoutError as error:
                logging.info("function took longer than %d seconds" % error.args[1])
            except ProcessExpired as error:
                logging.info("%s. Exit code: %d" % (error, error.exitcode))
            except Exception as error:
                logging.info("function raised %s" % error)
                logging.info(error.traceback)  # Python's traceback of remote process


def compute(function_codes, args):
    if not args['dir'] is None:
        write_string_append(f'{sys.argv}\n', f'{args["dir"]}/meta')
    for code in function_codes:
        process_single_function(args, code)

def main():
    args = vars(init_argparse())

    logging.basicConfig(
        filename=args['log'],
        level=logging.DEBUG,
        format='%(asctime)s.%(msecs)03d - %(funcName)s: %(message)s',
        datefmt='%m-%d %H:%M:%S',
    )

    if args['improve']:
        improve_in_parallel(args)
        return

    function_codes = get_function_codes(args)
    if args['sequential']:
        compute(function_codes, args)
    else:
        compute_in_parallel(function_codes, args)
    
if __name__ == "__main__":
    main()
