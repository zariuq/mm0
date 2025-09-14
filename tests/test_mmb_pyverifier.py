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
    build_symbols,
    run_proof_payload,
)
from mmb.cmd import read_cmd, Cmd, StmtOp, ProofOp, UnifyOp
from mmb.unify import run_unify
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
    fmt = load_mmb(mmb_path.read_bytes(), strict_align=False)
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
    fmt = load_mmb(mmb_path.read_bytes(), strict_align=False)
    te = fmt.terms[0]
    types = read_term_types(fmt, te)
    assert len(types) == te.num_args + 1


def test_thmentry_slice_bounds():
    mmb_path = ensure_peano_mmb()
    fmt = load_mmb(mmb_path.read_bytes(), strict_align=False)
    th = fmt.thms[0]
    params = read_thm_params(fmt, th)
    assert len(params) == th.num_args


def test_unify_reader_runs():
    mmb_path = ensure_peano_mmb()
    fmt = load_mmb(mmb_path.read_bytes(), strict_align=False)
    te = fmt.terms[0]
    prog = locate_unify_prog(fmt, te.p_args, te.num_args, True)
    u = UnifyReader(memoryview(fmt.data)[prog.start:prog.end])
    list(u.iter_cmds())
    with pytest.raises(ValueError):
        u_bad = UnifyReader(memoryview(b"\x45"))
        list(u_bad.iter_cmds())


def test_unify_vm_basic():
    # HYP, DUMMY 0, TERM_SAVE 0 (arity 2), REF 0, END
    buf = bytearray()
    buf += enc_cmd(UnifyOp.HYP)
    buf += enc_cmd(UnifyOp.DUMMY, 0)
    buf += enc_cmd(UnifyOp.TERM_SAVE, 0)
    buf += enc_cmd(UnifyOp.REF, 0)
    buf += enc_cmd(UnifyOp.END)
    res = run_unify(memoryview(bytes(buf)), lambda _: 2, outputs=1)
    assert len(res) == 1


def test_unify_vm_ref_oob():
    buf = enc_cmd(UnifyOp.REF, 0) + enc_cmd(UnifyOp.END)
    with pytest.raises(ValueError):
        run_unify(memoryview(buf), lambda _: 0, outputs=0)


def test_stmt_and_proof_scans():
    mmb_path = ensure_peano_mmb()
    fmt = load_mmb(mmb_path.read_bytes(), strict_align=False)
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


def test_stmt_payload_out_of_bounds(tmp_path):
    mmb_path = ensure_peano_mmb()
    data = bytearray(mmb_path.read_bytes())
    p_proof = int.from_bytes(data[24:28], "little")
    i = p_proof
    data[i] = (data[i] & 0x3F) | 0xC0
    data[i + 1 : i + 5] = (len(data) + 0x100).to_bytes(4, "little")
    bad = tmp_path / "stmt_overrun.mmb"
    bad.write_bytes(data)
    from mmb.format import StmtReader

    fmt = load_mmb(bad.read_bytes(), strict_index=False, strict_align=False)
    sr = StmtReader(fmt)
    with pytest.raises(Exception):
        sr.next()


def enc_cmd(op, data=0):
    if data == 0:
        tag = 0
        extra = b""
    elif data <= 0xFF:
        tag = 1
        extra = bytes([data])
    elif data <= 0xFFFF:
        tag = 2
        extra = data.to_bytes(2, "little")
    else:
        tag = 3
        extra = data.to_bytes(4, "little")
    return bytes([(op & 0x3F) | (tag << 6)]) + extra


def test_proofvm_stack_discipline_smoke():
    fmt = load_mmb(ensure_peano_mmb().read_bytes(), strict_align=False)
    sym = build_symbols(fmt)
    payload = bytearray()
    payload += enc_cmd(ProofOp.HYP)
    k0 = next((i for i, a in enumerate(sym.term_arity) if a == 0), None)
    if k0 is not None:
        payload += enc_cmd(ProofOp.TERM, k0)
    payload += enc_cmd(ProofOp.END)
    run_proof_payload(sym, memoryview(bytes(payload)))


def test_proofvm_underflow():
    fmt = load_mmb(ensure_peano_mmb().read_bytes(), strict_align=False)
    sym = build_symbols(fmt)
    k1 = next(i for i, a in enumerate(sym.term_arity) if a == 1)
    payload = enc_cmd(ProofOp.TERM, k1) + enc_cmd(ProofOp.END)
    with pytest.raises(Exception):
        run_proof_payload(sym, memoryview(payload))


def test_proofvm_ref_heap():
    fmt = load_mmb(ensure_peano_mmb().read_bytes(), strict_align=False)
    sym = build_symbols(fmt)
    payload = enc_cmd(ProofOp.HYP) + enc_cmd(ProofOp.SAVE) + enc_cmd(ProofOp.REF, 0) + enc_cmd(ProofOp.END)
    run_proof_payload(sym, memoryview(payload))


def test_proofvm_ref_oob():
    fmt = load_mmb(ensure_peano_mmb().read_bytes(), strict_align=False)
    sym = build_symbols(fmt)
    payload = enc_cmd(ProofOp.REF, 0) + enc_cmd(ProofOp.END)
    with pytest.raises(Exception):
        run_proof_payload(sym, memoryview(payload))


def test_proofvm_term_thm_save_ref():
    fmt = load_mmb(ensure_peano_mmb().read_bytes(), strict_align=False)
    sym = build_symbols(fmt)
    k0 = next((i for i, a in enumerate(sym.term_arity) if a == 0), None)
    t0 = next((i for i, a in enumerate(sym.thm_arity) if a == 0), None)
    payload = bytearray()
    if k0 is not None:
        payload += enc_cmd(ProofOp.TERM_SAVE, k0)
    if t0 is not None:
        payload += enc_cmd(ProofOp.THM_SAVE, t0)
    payload += enc_cmd(ProofOp.REF, 0) + enc_cmd(ProofOp.END)
    run_proof_payload(sym, memoryview(bytes(payload)))


def test_proofvm_cong_unimplemented():
    fmt = load_mmb(ensure_peano_mmb().read_bytes(), strict_align=False)
    sym = build_symbols(fmt)
    payload = enc_cmd(ProofOp.CONG) + enc_cmd(ProofOp.END)
    with pytest.raises(Exception):
        run_proof_payload(sym, memoryview(payload))

