#!/usr/bin/env python
# coding: utf-8

# In[1]:

from z3 import Int, Bool, Ints, Bools, Solver, Or, Not, And, BV2Int, BitVec, BitVecs, BitVecVal, BitVec, Concat, Extract, IntVal, Implies, CheckSatResult, Z3_L_TRUE
from typing import List

MAJ_BITVECTOR = 232

class Z3ModelWrapper()

    __init__(this, complexity, f, gate)
        this.solver = Solver()
        this.global_asserts = []
        this.global_vars = {}
        this.complexity = complexity
        this.f = f
        this.gate = gate

    def check(this)
        this.init_variables()

        for gate in right_inclusive_range(this.f.arity, this.f.arity + this.complexity)
            this.add_gate_constraints()

        for f_input_value in range(this.f.bitlength)
            this.add_zero_input_constraint()       
            this.add_function_semantics_constraint()
            this.add_connect_gate_inputs_to_f_inputs_constraint()
            
            for gate in right_inclusive_range(f_arity, f_arity + complexity)
                add_majority_functionality_constraint(f_input_value, gate)            
                add_input_connections_constraint()

    def add_gate_constraints(this, gate)
        for gate_input in right_inclusive_range(0, this.gate.arity)        
            s = this.global_vars[f'gate_input_number_{gate}_{gate_input}']
            
            # нет циклов
            this.add_assert(s  gate)

            # номера операндов неотрицательны
            this.add_assert(s = 0)

            # TODO generalize
        # номера операндов упорядоченны
        s1 = this.global_vars[f'gate_input_number_{gate}_1']
        s2 = this.global_vars[f'gate_input_number_{gate}_2']
        s3 = this.global_vars[f'gate_input_number_{gate}_3']
        
        this.add_assert(s1  s2, s2  s3)
        
        # TODO generalize
        # (Оптимиз.) не более одного операнда инвертировано
        p1 = this.global_vars[f'gate_input_polarity_{gate}_1']
        p2 = this.global_vars[f'gate_input_polarity_{gate}_2']
        p3 = this.global_vars[f'gate_input_polarity_{gate}_3']
        
        this.add_assert(((p1  p2) & (p2  p3) & (p1  p3)) == 1)


    def add_majority_functionality_constraint(this, f_input_value, gate)
        # TODO generalize
        a1 = this.global_vars[f'gate_input_value_{f_input_value}_{gate}_1']
        a2 = this.global_vars[f'gate_input_value_{f_input_value}_{gate}_2']
        a3 = this.global_vars[f'gate_input_value_{f_input_value}_{gate}_3']
        
        b = this.global_vars[f'gate_output_value_{f_input_value}_{gate}']
        this.add_assert(b == ((a1  a2) & (a1  a3) & (a2  a3)))


    def add_function_semantics_constraint(this, f_input_value)
        bt_out = this.global_vars[f'gate_output_value_{f_input_value}_{this.f.arity + this.complexity}']
        p_out = this.global_vars['output_polarity']
        f = this.global_vars['f']
        i = f_input_value
        this.add_assert(bt_out == ~p_out + Extract(i, i, f))


    def add_input_connections_constraint(this, f_input_value, gate)
        for gate_input in right_inclusive_range(0, this.gate.arity)
            a = this.global_vars[f'gate_input_value_{f_input_value}_{gate}_{gate_input}']
            p = this.global_vars[f'gate_input_polarity_{gate}_{gate_input}']
            s = this.global_vars[f'gate_input_number_{gate}_{gate_input}']
            
            for j in range(0, gate)
                b = this.global_vars[f'gate_output_value_{f_input_value}_{j}']
                this.add_assert(Implies(s == j, a == b + ~p))


    def add_connect_gate_inputs_to_f_inputs_constraint(this, f_input_value)
        # выходы bi элементов xi, 1 = i = f_arity === входы функции f
        for gate in right_inclusive_range(0, this.f.arity)
            bti = this.global_vars[f'gate_output_value_{f_input_value}_{gate}']
            this.add_assert(bti == int2bitvec(this.f.arity, f_input_value)[gate - 1])


    def add_zero_input_constraint(this, f_input_value)
        bt0 = this.global_vars[f'gate_output_value_{f_input_value}_0']
        this.add_assert(bt0 == 0)

        
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


def bitvec2int(bitvec : List[bool]) -> int:
    result = 0
    for i, xi in enumerate(bitvec):
        xi = bool2int(xi)
        result += xi * (2 ** i)
    return result


def int2bitvec(n : int, i : int) -> List[bool]:
    result = []
    for _ in range(n):
        if (i > 0):
            result.append(i & 1)
            i >>= 1
        else:
            result.append(0)
    return result


"""
f - битовый вектор длины 2 ** n
x - битовый вектор длины n
"""
def evaluate_fun(f: List[bool], x: List[bool]) -> bool:
    n = len(x)
    if (len(f) != 2 ** n):
        raise Exception("Bad arguments")
    x = bitvec2int(x)
    return f[x]


def z3_evaluate_fun(f, x):
    return f[BV2Int(x)]


def right_inclusive_range(start, end):
    return range(start + 1, end + 1)


def create_bitvec(global_vars, name, bitlength):
    global_vars[name] = BitVec(name, bitlength)


def create_int(global_vars, name):
    global_vars[name] = Int(name)

  
def add_assert(global_asserts, *asserts):
    for a in asserts:
        global_asserts.append(a)


def init_variables(complexity, f_bitvector, f_arity, f_bitlength, gate_bitvector, gate_arity, gate_bitlength):
    global_vars = {}

    global_vars['gate'] = BitVec('gate', gate_bitlength)
    global_vars['gate_value'] = BitVecVal(gate_bitvector, gate_bitlength) # try to remove this line
    global_vars['f'] = BitVecVal(f_bitvector, f_bitlength)
    create_bitvec(global_vars, 'output_polarity', 1)

    for gate in right_inclusive_range(f_arity, f_arity + complexity):
        for gate_input in right_inclusive_range(0, gate_arity):
            create_bitvec(global_vars, f'gate_input_polarity_{gate}_{gate_input}', 1)
            create_int(global_vars, f'gate_input_number_{gate}_{gate_input}')

    for f_input_value in range(f_bitlength):
        # bt0 = 0
        create_bitvec(global_vars, f'gate_output_value_{f_input_value}_0', 1)
        
        # bti - f input values (xi, 1 <= i <= n - f inputs)
        for gate in right_inclusive_range(0, f_arity):
            create_bitvec(global_vars, f'gate_output_value_{f_input_value}_{gate}', 1)
        
        for gate in right_inclusive_range(f_arity, f_arity + complexity):
            # bti - gate output values (xi, n < i <= n + r - gates)
            create_bitvec(global_vars, f'gate_output_value_{f_input_value}_{gate}', 1)
            
            # atic - gate input values
            for gate_input in right_inclusive_range(0, gate_arity):
                create_bitvec(global_vars, f'gate_input_value_{f_input_value}_{gate}_{gate_input}', 1)
    
    return global_vars


def add_gate_constraints(global_vars, global_asserts, gate, gate_arity):
    for gate_input in right_inclusive_range(0, gate_arity):        
        s = global_vars[f'gate_input_number_{gate}_{gate_input}']
        
        # нет циклов
        add_assert(global_asserts, s < gate)

        # номера операндов неотрицательны
        add_assert(global_asserts, s >= 0)

        # TODO: generalize
    # номера операндов упорядоченны
    s1 = global_vars[f'gate_input_number_{gate}_1']
    s2 = global_vars[f'gate_input_number_{gate}_2']
    s3 = global_vars[f'gate_input_number_{gate}_3']
    
    add_assert(global_asserts, s1 < s2, s2 < s3)
    
    # TODO: generalize
    # (Оптимиз.) не более одного операнда инвертировано
    p1 = global_vars[f'gate_input_polarity_{gate}_1']
    p2 = global_vars[f'gate_input_polarity_{gate}_2']
    p3 = global_vars[f'gate_input_polarity_{gate}_3']
    
    add_assert(global_asserts, ((p1 | p2) & (p2 | p3) & (p1 | p3)) == 1)


def add_majority_functionality_constraint(global_vars, global_asserts, f_input_value, gate):
    # TODO: generalize
    a1 = global_vars[f'gate_input_value_{f_input_value}_{gate}_1']
    a2 = global_vars[f'gate_input_value_{f_input_value}_{gate}_2']
    a3 = global_vars[f'gate_input_value_{f_input_value}_{gate}_3']
    
    b = global_vars[f'gate_output_value_{f_input_value}_{gate}']
    add_assert(global_asserts, b == ((a1 | a2) & (a1 | a3) & (a2 | a3)))


def add_function_semantics_constraint(global_vars, global_asserts, f_input_value, f_arity, complexity):
    bt_out = global_vars[f'gate_output_value_{f_input_value}_{f_arity + complexity}']
    p_out = global_vars['output_polarity']
    f = global_vars['f']
    i = f_input_value
    add_assert(global_asserts, bt_out == ~p_out + Extract(i, i, f))


def add_input_connections_constraint(global_vars, global_asserts, f_input_value, gate, gate_arity):
    for gate_input in right_inclusive_range(0, gate_arity):
        a = global_vars[f'gate_input_value_{f_input_value}_{gate}_{gate_input}']
        p = global_vars[f'gate_input_polarity_{gate}_{gate_input}']
        s = global_vars[f'gate_input_number_{gate}_{gate_input}']
        
        for j in range(0, gate):
            b = global_vars[f'gate_output_value_{f_input_value}_{j}']
            add_assert(global_asserts, Implies(s == j, a == b + ~p))


def add_connect_gate_inputs_to_f_inputs_constraint(global_vars, global_asserts, f_input_value, f_arity):
    # выходы bi элементов xi, 1 <= i <= f_arity === входы функции f
    for gate in right_inclusive_range(0, f_arity):
        bti = global_vars[f'gate_output_value_{f_input_value}_{gate}']
        add_assert(global_asserts, bti == int2bitvec(f_arity, f_input_value)[gate - 1])


def add_zero_input_constraint(global_vars, global_asserts, f_input_value):
    bt0 = global_vars[f'gate_output_value_{f_input_value}_0']
    add_assert(global_asserts, bt0 == 0)


def try_complexity(complexity, solver):
    global_asserts = []
    
    # synthesized function
    # f_bitvector = ~0b0111
    f_bitvector = ~0b10010110 # full adder
    f_arity = 5
    f_bitlength = 2 ** f_arity
    
    gate_bitvector = MAJ_BITVECTOR
    gate_arity = 3
    gate_bitlength = 2 ** gate_arity 

    global_vars = init_variables(complexity, f_bitvector, f_arity, f_bitlength, gate_bitvector, gate_arity, gate_bitlength)

    for gate in right_inclusive_range(f_arity, f_arity + complexity):
        add_gate_constraints(global_vars, global_asserts, gate, gate_arity)

    for f_input_value in range(f_bitlength):
        add_zero_input_constraint(global_vars, global_asserts, f_input_value)       
        add_function_semantics_constraint(global_vars, global_asserts, f_input_value, f_arity, complexity)
        add_connect_gate_inputs_to_f_inputs_constraint(global_vars, global_asserts, f_input_value, f_arity)
        
        for gate in right_inclusive_range(f_arity, f_arity + complexity):
            add_majority_functionality_constraint(global_vars, global_asserts, f_input_value, gate)            
            add_input_connections_constraint(global_vars, global_asserts, f_input_value, gate, gate_arity)
            
    solver.add([i for i in global_asserts])
    return solver.check() == CheckSatResult(Z3_L_TRUE)

max_complexity = 10
# for f in range(0xffff):
for complexity in range(max_complexity):
    solver = Solver()
    if try_complexity(complexity, solver):
        print(f'MIN COMPLEXITY FOUND: {complexity}')
        break
"""
model = solver.model()
d = {i.name() : model.get_interp(i) for i in model}
for key, value in d.items():
    print(f'{key} : {value}')

import re

gate_output_pattern = re.compile(r'gate_output_value_(?P<f_input_value>[0-9]+?)_(?P<gate>[0-9]+?)')
gate_input_pattern = re.compile(r'gate_input_value_(?P<f_input_value>[0-9]+)_(?P<gate>[0-9]+)_(?P<gate_input>[0-9]+)')
table = { 'raw_input_1' : [], 'raw_input_2' : [], 'raw_input_3' : [], 'p_input_1' : [], 'p_input_2' : [], 'p_input_3' : [], 'output' : []}
for name, value in sorted(d.items()):

    m = gate_input_pattern.match(name)
#    print(m)
    if not m is None:
        f_input_value = int(m.group('f_input_value'))      
        gate = int(m.group('gate'))
        gate_input = int(m.group('gate_input'))
        table[f'p_input_{gate_input}'].append(value)

    m = gate_output_pattern.match(name)
#    print(m)
    if not m is None:
        f_input_value = f_input_value = int(m.group('f_input_value'))
        gate = int(m.group('gate'))
        if gate == 4:
            table['output'].append(value)
        elif gate >= 1 and gate <= 3:
            table[f'raw_input_{gate}'].append(value)


for key, value in table.items():
    print(f'{key:>15} : {value}')
    
"""
print(f'{mincode}\nmig\n{complexity}\n)