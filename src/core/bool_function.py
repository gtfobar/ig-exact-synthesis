from utils import get_mincode

class BoolFunction():
    MAJ_CODE = 0b00010111
    FULLADDER_CODE= 0b01101001

    def __init__(this, code, arity):
        this.code = code
        this.arity = arity
        this.bitlength = 2 ** arity
        this.mincode = get_mincode(this.code, this.arity)

    def is_normal():
        mask = 1 << (this.bitlength - 1)
        return 1 if (this.code & mask) else 0