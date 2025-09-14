import sys
import pathlib
import pytest

sys.path.append(str(pathlib.Path(__file__).resolve().parents[1]))

from mmb.io import BR
from mmb.verify import verify_mmb
from mmb.format import (
    load_mmb,
    decode_type,
    read_term_types,
    read_thm_params,
    locate_unify_prog,
    UnifyReader,
    StmtReader,
    ProofReader,
)
from mmb.cmd import read_cmd, Cmd, StmtOp, ProofOp, UnifyOp
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


def test_cmd_encoding_roundtrip():
    buf = bytes([
        0x05,  # DATA0 op=5
        0x45, 0x7F,  # DATA8 op=5 data=0x7F
        0x85, 0x34, 0x12,  # DATA16 op=5 data=0x1234
        0xC5, 0x78, 0x56, 0x34, 0x12,  # DATA32 op=5 data=0x12345678
    ])
    r = BR(buf)
    assert read_cmd(r) == Cmd(5, 0)
    assert read_cmd(r) == Cmd(5, 0x7F)
    assert read_cmd(r) == Cmd(5, 0x1234)
    assert read_cmd(r) == Cmd(5, 0x12345678)


def test_type_decode_boundaries():
    u = (1 << 63) | (127 << 56) | ((1 << 56) - 1)
    t = decode_type(u)
    assert t.bound and t.sort == 127 and t.deps == (1 << 56) - 1
    t2 = decode_type(0)
    assert not t2.bound and t2.sort == 0 and t2.deps == 0


def test_termentry_slice_bounds():
    mmb_path = ensure_peano_mmb()
    fmt = load_mmb(mmb_path.read_bytes())
    te = fmt.terms[0]
    types = read_term_types(fmt, te)
    assert len(types) == te.num_args + 1


def test_thmentry_slice_bounds():
    mmb_path = ensure_peano_mmb()
    fmt = load_mmb(mmb_path.read_bytes())
    th = fmt.thms[0]
    params = read_thm_params(fmt, th)
    assert len(params) == th.num_args


def test_unify_reader_runs():
    mmb_path = ensure_peano_mmb()
    fmt = load_mmb(mmb_path.read_bytes())
    te = fmt.terms[0]
    prog = locate_unify_prog(fmt, te.p_args, te.num_args, True)
    u = UnifyReader(memoryview(fmt.data)[prog.start:prog.end])
    list(u.iter_cmds())
    with pytest.raises(ValueError):
        u_bad = UnifyReader(memoryview(b"\x45"))
        list(u_bad.iter_cmds())


def test_stmt_and_proof_scans():
    mmb_path = ensure_peano_mmb()
    fmt = load_mmb(mmb_path.read_bytes())
    sr = StmtReader(fmt)
    sorts = terms = thms = 0
    while True:
        st = sr.next()
        if st is None:
            break
        if st.op == StmtOp.SORT:
            sorts += 1
        elif st.op in (StmtOp.TERM, StmtOp.DEF, StmtOp.LOCAL_DEF):
            terms += 1
        elif st.op in (StmtOp.AXIOM, StmtOp.THM, StmtOp.LOCAL_THM):
            thms += 1
        if st.proof is not None:
            pr = ProofReader(st.proof)
            list(pr.iter_cmds())
    assert sorts == fmt.num_sorts
    assert terms == fmt.num_terms
    assert thms == fmt.num_thms


def test_br_and_check_ptr_negatives():
    r = BR(b"\x00")
    with pytest.raises(ValueError):
        r.take(2)
    from mmb.io import check_ptr

    with pytest.raises(ValueError):
        check_ptr(1, 1, 1, 1)

