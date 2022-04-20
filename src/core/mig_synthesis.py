import z3
import argparse
import sys
import logging, sys
from utils import right_inclusive_range, int2bitvec, bitvec2int, get_latest_function_synthesized, get_mincode

logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)
z3.set_param('parallel.enable', True)
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

class BoolFunction():
    MAJ_CODE = 0b00010111
    FULLADDER_CODE= 0b01101001

    def __init__(this, code, arity):
        this.code = code
        this.arity = arity
        this.bitlength = 2 ** arity
        this.mincode = get_mincode(this.code, this.arity)

class Z3ModelWrapper():

    def __init__(this, complexity, f, gate):
        this.solver = z3.Solver()
        this.asserts = []
        this.vars = {}
        this.complexity = complexity
        this.f = f
        this.gate = gate
        this.check_result = None

    def evaluate_f(this, x):
        i = this.f.bitlength - x - 1
        f = this.vars['f']
        return z3.Extract(i, i, f)

    def eval(this, expr):
        if this.check_result is None:
            raise Exception("Call Z3ModelWrapper.check() first")
        return this.solver.model().eval(expr)

    def __str__(this):
        if this.f.mincode != this.f.code:
            logging.info('code != mincode  =>  skipping\n')
            return ''

        if not this.check_result:
            return 'unsat'

        polarity = this.eval(~this.vars['output_polarity'])
        result = f'{this.f.mincode}\nmig\n{this.complexity}\n{this.f.arity + this.complexity} {polarity}\n'

        for gate in right_inclusive_range(this.f.arity, this.f.arity + this.complexity):
            for gate_input in right_inclusive_range(0, this.gate.arity):
                s = this.vars[f'gate_input_{gate}_{gate_input}']
                p = this.vars[f'gate_input_polarity_{gate}_{gate_input}']
                result += f'{this.eval(s)} {this.eval(~p)} '
        return result

    def check(this):
        if (not this.check_result is None):
            return this.check_result

        this.init_variables()

        for gate in right_inclusive_range(this.f.arity, this.f.arity + this.complexity):
            this.add_gate_constraints(gate)

        for f_input_value in range(this.f.bitlength):
            this.add_zero_input_constraint(f_input_value)       
            this.add_function_semantics_constraint(f_input_value)
            this.add_connect_gate_inputs_to_f_inputs_constraint(f_input_value)
            
            for gate in right_inclusive_range(this.f.arity, this.f.arity + this.complexity):
                this.add_majority_functionality_constraint(f_input_value, gate)            
                this.add_input_connections_constraint(f_input_value, gate)
        
        this.solver.add([i for i in this.asserts])
        this.check_result = this.solver.check() == z3.CheckSatResult(z3.Z3_L_TRUE)
        return this.check_result

    def init_variables(this):
        # this line can be removed, because gate semantics is given solely by constraints
        # this.vars['gate'] = z3.BitVec('gate', this.gate.bitlength)
        this.vars['f'] = z3.BitVecVal(this.f.code, this.f.bitlength)
        this.create_bitvec('output_polarity', 1)

        for gate in right_inclusive_range(this.f.arity, this.f.arity + this.complexity):
            for gate_input in right_inclusive_range(0, this.gate.arity):
                this.create_bitvec(f'gate_input_polarity_{gate}_{gate_input}', 1)
                this.create_int(f'gate_input_{gate}_{gate_input}')

        for f_input_value in range(this.f.bitlength):
            # bt0 = 0
            this.create_bitvec(f'gate_output_value_{f_input_value}_0', 1)
            
            # bti - f input values (xi, 1 <= i <= n - f inputs)
            for gate in right_inclusive_range(0, this.f.arity):
                this.create_bitvec(f'gate_output_value_{f_input_value}_{gate}', 1)
            
            for gate in right_inclusive_range(this.f.arity, this.f.arity + this.complexity):
                # bti - gate output values (xi, n < i <= n + r - gates)
                this.create_bitvec(f'gate_output_value_{f_input_value}_{gate}', 1)
                
                # atic - gate input values
                for gate_input in right_inclusive_range(0, this.gate.arity):
                    this.create_bitvec(f'gate_input_value_{f_input_value}_{gate}_{gate_input}', 1)

    def add_gate_constraints(this, gate):
        for gate_input in right_inclusive_range(0, this.gate.arity):
            s = this.vars[f'gate_input_{gate}_{gate_input}']
            
            # нет циклов
            this.add_assert(s < gate)

            # номера операндов неотрицательны
            this.add_assert(s >= 0)

            # TODO generalize
        # номера операндов упорядоченны
        s1 = this.vars[f'gate_input_{gate}_1']
        s2 = this.vars[f'gate_input_{gate}_2']
        s3 = this.vars[f'gate_input_{gate}_3']
        
        this.add_assert(s1 < s2, s2 < s3)
        
        # TODO generalize
        # (Оптимиз.) не более одного операнда инвертировано
        p1 = this.vars[f'gate_input_polarity_{gate}_1']
        p2 = this.vars[f'gate_input_polarity_{gate}_2']
        p3 = this.vars[f'gate_input_polarity_{gate}_3']
        
        this.add_assert(((p1 | p2) & (p2 | p3) & (p1 | p3)) == 1)

    def add_majority_functionality_constraint(this, f_input_value, gate):
        # TODO generalize
        a1 = this.vars[f'gate_input_value_{f_input_value}_{gate}_1']
        a2 = this.vars[f'gate_input_value_{f_input_value}_{gate}_2']
        a3 = this.vars[f'gate_input_value_{f_input_value}_{gate}_3']
        
        b = this.vars[f'gate_output_value_{f_input_value}_{gate}']
        this.add_assert(b == ((a1 | a2) & (a1 | a3) & (a2 | a3)))

    def add_function_semantics_constraint(this, f_input_value):
        bt_out = this.vars[f'gate_output_value_{f_input_value}_{this.f.arity + this.complexity}']
        p_out = this.vars['output_polarity']
        f = this.evaluate_f(f_input_value)
        this.add_assert(bt_out == ~p_out + f)


    def add_input_connections_constraint(this, f_input_value, gate):
        for gate_input in right_inclusive_range(0, this.gate.arity):
            a = this.vars[f'gate_input_value_{f_input_value}_{gate}_{gate_input}']
            p = this.vars[f'gate_input_polarity_{gate}_{gate_input}']
            s = this.vars[f'gate_input_{gate}_{gate_input}']
            
            for j in range(0, gate):
                b = this.vars[f'gate_output_value_{f_input_value}_{j}']
                this.add_assert(z3.Implies(s == j, a == b + ~p))

    def add_connect_gate_inputs_to_f_inputs_constraint(this, f_input_value):
        # выходы bi элементов xi, 1 = i = this.f.arity === входы функции f
        for gate in right_inclusive_range(0, this.f.arity):
            bti = this.vars[f'gate_output_value_{f_input_value}_{gate}']
            this.add_assert(bti == int2bitvec(this.f.arity, f_input_value)[gate - 1])

    def add_zero_input_constraint(this, f_input_value):
        bt0 = this.vars[f'gate_output_value_{f_input_value}_0']
        this.add_assert(bt0 == 0)

    def create_bitvec(this, name, bitlength):
        this.vars[name] = z3.BitVec(name, bitlength)

    def create_int(this, name):
        this.vars[name] = z3.Int(name)
    
    def add_assert(this, *asserts):
        for a in asserts:
            this.asserts.append(a)

def synthesize_mig(code, max_complexity=MAX_COMPLEXITY):
    f = BoolFunction(code, 5)
    gate = BoolFunction(BoolFunction.MAJ_CODE, 3)

    for complexity in range(max_complexity + 1):
        logging.info(f'checking {complexity}...')
        m = Z3ModelWrapper(complexity, f, gate)
        if m.check():
            logging.info('***** sat *****\n')
            return m
        logging.info('unsat')

def check_complexity(code, complexity):
    f = BoolFunction(code, 5)
    gate = BoolFunction(BoolFunction.MAJ_CODE, 3)

    m = Z3ModelWrapper(complexity, f, gate)
    logging.info(f'checking {complexity}...')
    if m.check():
        logging.info('***** sat *****\n')
    else:
        logging.info('unsat')
    return m

def to_dir(codes, args):
    for code in codes:
        logging.info(f'***** Function {code} *****')
        with open(f'{args.dir}/{code}', 'w+') as output:
            if args.check is None:
                m = synthesize_mig(code, MAX_COMPLEXITY + 1)
            else:
                m = check_complexity(code, args.check)
            output.write(str(m))

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
    
    return function_codes

def main():
    args = init_argparse()
    function_codes = get_function_codes(args)
    print(function_codes)

    global MAX_COMPLEXITY
    if args.max_complexity is not None:
        MAX_COMPLEXITY = args.max_complexity

    if args.dir is not None:
        to_dir(function_codes, args)
        return

    if args.output is None:
        output = sys.stdout
    else:
        with open(f'{args.output}.meta', 'a+') as meta:
            meta.write(str(sys.argv))
        output = open(args.output, 'a+')
        
    for code in function_codes:
        if args.check is None:
            m = synthesize_mig(code, max_complexity)
        else:
            m = check_complexity(code, args.check)
        output.write(str(m))
        
    if not args.output is None:
        output.close()
    
if __name__ == "__main__":
    main()
