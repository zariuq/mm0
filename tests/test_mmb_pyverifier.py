import io
import os
import subprocess
import pytest
import pathlib
import sys

sys.path.append(str(pathlib.Path(__file__).resolve().parents[1]))


from mmb.io import BR
from mmb.verify import verify_mmb
from mmb.format import load_mmb


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


@pytest.mark.skipif(not pathlib.Path("examples/peano.mmb").exists(), reason="peano.mmb missing")
def test_verify_structural_load():
    verify_mmb("examples/peano.mm0", "examples/peano.mmb")


@pytest.mark.skipif(
    not pathlib.Path("examples/peano.mmb").exists(),
    reason="peano.mmb missing",
)
def test_header_and_counts_peano():
    fmt = load_mmb(open("examples/peano.mmb", "rb").read())
    assert fmt.num_sorts == 3
    assert fmt.num_terms == 170
    assert fmt.num_thms == 2689
    assert isinstance(fmt.strings, list) and len(fmt.strings) > 10


@pytest.mark.skipif(
    not pathlib.Path("examples/peano.mmb").exists(),
    reason="peano.mmb missing",
)
def test_truncated_file_raises(tmp_path):
    p = tmp_path / "peano_trunc.mmb"
    data = open("examples/peano.mmb", "rb").read()
    p.write_bytes(data[:100])
    with pytest.raises(ValueError):
        load_mmb(p.read_bytes())

