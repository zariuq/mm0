import sys
import pathlib
import pytest

sys.path.append(str(pathlib.Path(__file__).resolve().parents[1]))

from mmb.io import BR
from mmb.verify import verify_mmb
from mmb.format import load_mmb
from test_mmb import ensure_peano_mmb


def test_varu_roundtrip_basic():
    def enc(x: int) -> bytes:
        out = bytearray()
        while True:
            b = x & 0x7F
            x >>= 7
            out.append(b | (0x80 if x else 0))
            if not x:
                return bytes(out)
    for v in [0, 1, 2, 127, 128, 129, 16384, 2 ** 31 - 1]:
        assert BR(enc(v)).varu() == v


def test_verify_structural_load():
    mmb_path = ensure_peano_mmb()
    verify_mmb("examples/peano.mm0", str(mmb_path))


def test_header_and_counts_peano():
    mmb_path = ensure_peano_mmb()
    fmt = load_mmb(mmb_path.read_bytes())
    assert fmt.num_sorts == 3
    assert fmt.num_terms == 170
    assert fmt.num_thms == 2689
    assert isinstance(fmt.strings, list) and len(fmt.strings) > 10

