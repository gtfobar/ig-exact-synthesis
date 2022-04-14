import pytest
from core.utils import int2bitvec, bitvec2int

testdata =     [
        (
            24,
            [0, 0, 0, 1, 1, 0, 0, 0],
            8
        ),
        (
            127,
            [0, 1, 1, 1, 1, 1, 1, 1],
            8
        ),
        (
            105,
            [0, 1, 1, 0, 1, 0, 0, 1],
            8
        ),
        (
            872,
            [0, 0, 0, 0, 0, 0, 1, 1,  0, 1, 1, 0,  1, 0, 0, 0],
            16
        ),
        (
            395233,
            [0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 1, 1, 0,  0, 0, 0, 0,  0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1],
            32
        )

    ]

@pytest.mark.parametrize(
    "i,bitvec,n", testdata
)
def test_int2bitvec(n, i, bitvec):
    print(int2bitvec(n, ~i))
    print(int2bitvec(n, i))
    print(bitvec)

    assert int2bitvec(n, i) == bitvec
    # assert int2bitvec(bitvec2int(bitvec), n) == bitvec

@pytest.mark.parametrize(
    "i,bitvec,n", testdata
)
def test_bitvec2int(n, i, bitvec):
    assert bitvec2int(bitvec) == i
    assert len(bitvec) == n
    # assert bitvec2int(int2bitvec(i, n)) == i