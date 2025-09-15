"""Structural loader for `.mmb` files."""
from __future__ import annotations

from dataclasses import dataclass

from .io import BR, check_ptr
from .ast import Expr


@dataclass
class TypeInfo:
    """Decoded argument type (mm0b_parser `Type`)."""

    bound: bool
    sort: int
    deps: int


def decode_type(u: int) -> TypeInfo:
    """Decode a 64-bit packed `Type` value.

    Mirrors `mm0-rs/components/mm0b_parser/src/ty.rs` bit layout."""

    return TypeInfo(
        bound=bool((u >> 63) & 1),
        sort=(u >> 56) & 0x7F,
        deps=u & ((1 << 56) - 1),
    )


@dataclass
class TermEntry:
    """Term metadata entry (mm0-rs `TermEntry`)."""

    num_args: int
    sort: int
    p_args: int


@dataclass
class ThmEntry:
    """Theorem metadata entry (mm0-rs `ThmEntry`)."""

    num_args: int
    p_args: int


@dataclass
class MMBFile:
    """Top-level structure information extracted from an MMB file."""

    data: bytes
    num_sorts: int
    num_terms: int
    num_thms: int
    p_terms: int
    p_thms: int
    p_proof: int
    sorts: list[int]
    strings: list[str]
    terms: list[TermEntry]
    thms: list[ThmEntry]


def proof_slice(m: MMBFile) -> memoryview:
    """Return the proof stream region as a memoryview."""

    return memoryview(m.data)[m.p_proof :]


def _cstr(data: bytes, off: int) -> str:
    end = data.find(b"\0", off)
    if end == -1:
        raise ValueError("unterminated string")
    return data[off:end].decode("utf-8")


def load_mmb(
    data: bytes,
    *,
    strict_index: bool = False,
    strict_align: bool = True,
) -> MMBFile:
    """Parse header, index and declaration tables.

    Mirrors `mm0-rs/src/mmb/import.rs` structure loader.

    If ``strict_index`` is false, a malformed or missing index does not
    raise; instead ``strings`` will be empty."""

    n = len(data)
    r = BR(data)
    if r.take(4).tobytes() != b"MM0B":
        raise ValueError("bad magic")
    version = r.u8()
    if version != 1:
        raise ValueError(f"unsupported version {version}")
    num_sorts = r.u8()
    r.take(2)
    num_terms = r.u32()
    num_thms = r.u32()
    p_terms = r.u32()
    p_thms = r.u32()
    p_proof = r.u32()
    r.u32()
    p_index = r.u64()

    sorts = list(r.take(num_sorts).tobytes())

    base = 40 + num_sorts
    if not (base <= p_terms <= p_thms <= p_proof <= n):
        raise ValueError("section offsets out of range")
    align = 8 if strict_align else 4
    for ptr in (p_terms, p_thms, p_proof):
        check_ptr(ptr, align, 0, n)
    if p_index:
        try:
            check_ptr(p_index, 8, 0, n)
        except ValueError:
            if strict_index:
                raise
            p_index = 0

    terms: list[TermEntry] = []
    if num_terms:
        check_ptr(p_terms, 4, 8 * num_terms, n)
        tr = BR(data[p_terms:p_thms])
        for _ in range(num_terms):
            num_args = tr.u16()
            sort = tr.u8()
            tr.u8()
            p_args = tr.u32()
            check_ptr(p_args, 8, 8 * (num_args + 1), n)
            terms.append(TermEntry(num_args, sort, p_args))

    thms: list[ThmEntry] = []
    if num_thms:
        check_ptr(p_thms, 4, 8 * num_thms, n)
        tr = BR(data[p_thms:p_proof])
        for _ in range(num_thms):
            num_args = tr.u16()
            tr.u16()
            p_args = tr.u32()
            check_ptr(p_args, 8, 8 * num_args, n)
            thms.append(ThmEntry(num_args, p_args))

    strings: list[str] = []
    if p_index:
        try:
            ir = BR(data[p_index:])
            ir.take(8)  # p_root
            name_ptr = 0
            while ir.i + 16 <= ir.n:
                idb = ir.take(4).tobytes()
                ir.u32()
                ptr = ir.u64()
                if idb == b"Name":
                    name_ptr = ptr
            if name_ptr:
                count = num_sorts + num_terms + num_thms
                check_ptr(name_ptr, 8, 16 * count, n)
                off = name_ptr
                for _ in range(count):
                    off += 8
                    p_name = int.from_bytes(data[off:off+8], "little")
                    off += 8
                    check_ptr(p_name, 1, 1, n)
                    strings.append(_cstr(data, p_name))
        except ValueError:
            if strict_index:
                raise
            strings = []

    return MMBFile(
        data=data,
        num_sorts=num_sorts,
        num_terms=num_terms,
        num_thms=num_thms,
        p_terms=p_terms,
        p_thms=p_thms,
        p_proof=p_proof,
        sorts=sorts,
        strings=strings,
        terms=terms,
        thms=thms,
    )


def read_term_types(m: MMBFile, te: TermEntry) -> list[TypeInfo]:
    """Read the argument and return types for a term."""

    start = te.p_args
    end = start + 8 * (te.num_args + 1)
    check_ptr(start, 8, end - start, len(m.data))
    r = BR(m.data[start:end])
    return [decode_type(r.u64()) for _ in range(te.num_args + 1)]


def read_thm_params(m: MMBFile, th: ThmEntry) -> list[TypeInfo]:
    """Read the parameter types for a theorem."""

    start = th.p_args
    end = start + 8 * th.num_args
    check_ptr(start, 8, end - start, len(m.data))
    r = BR(m.data[start:end])
    return [decode_type(r.u64()) for _ in range(th.num_args)]


@dataclass
class SymbolTable:
    """Arity/definition metadata for term and theorem references."""

    term_arity: list[int]
    thm_arity: list[int]
    term_defs: list[Expr | None]


def build_symbols(m: MMBFile) -> SymbolTable:
    """Build a symbol table capturing term/theorem arities."""

    return SymbolTable(
        term_arity=[te.num_args for te in m.terms],
        thm_arity=[th.num_args for th in m.thms],
        term_defs=[None] * len(m.terms),
    )


@dataclass
class UnifyProg:
    start: int
    end: int


def locate_unify_prog(m: MMBFile, p_args: int, n_args: int, is_term: bool) -> UnifyProg:
    """Locate the unify program following an arg array."""

    start = p_args + 8 * (n_args + (1 if is_term else 0))
    candidates = [m.p_terms, m.p_thms, m.p_proof, len(m.data)]
    candidates.extend(t.p_args for t in m.terms)
    candidates.extend(th.p_args for th in m.thms)
    end = min(c for c in candidates if c > start)
    return UnifyProg(start, end)


class UnifyReader:
    """Decode-only iterator over a unify stream."""

    def __init__(self, buf: memoryview):
        self.r = BR(buf)

    def iter_cmds(self):
        from .cmd import read_cmd, UnifyOp

        while True:
            c = read_cmd(self.r)
            if c.op == UnifyOp.END:
                break
            yield c


@dataclass
class Stmt:
    op: int
    data: int
    off: int
    proof: memoryview | None


class StmtReader:
    """Iterator over the statement stream at ``p_proof``."""

    def __init__(self, m: MMBFile):
        buf = proof_slice(m)
        self.r = BR(buf)
        self.base = m.p_proof

    def next(self) -> Stmt | None:
        from .cmd import read_cmd, StmtOp

        if self.r.i >= self.r.n:
            return None
        off_rel = self.r.i
        off = self.base + off_rel
        c = read_cmd(self.r)
        if c.op == StmtOp.END:
            return None
        proof_start = self.r.i
        stmt_end = off_rel + c.data
        if stmt_end > self.r.n:
            raise ValueError("statement payload out of bounds")
        proof = None
        if proof_start < stmt_end:
            proof = self.r.b[proof_start:stmt_end]
        self.r.i = stmt_end
        return Stmt(c.op, c.data, off, proof)


class ProofReader:
    """Decode-only iterator over a proof stream."""

    def __init__(self, buf: memoryview):
        self.r = BR(buf)

    def iter_cmds(self):
        from .cmd import read_cmd, ProofOp

        while True:
            c = read_cmd(self.r)
            if c.op == ProofOp.END:
                break
            yield c


def run_proof_payload(
    sym: SymbolTable,
    buf: memoryview,
    *,
    goal: "Eq" | None = None,
    require_goal: bool = True,
) -> None:
    """Execute a proof payload with convertibility checks and an optional goal."""

    from .cmd import read_cmd, ProofOp
    from .vm import ProofVM, VMError

    vm = ProofVM(sym)
    vm.goal = goal
    r = BR(buf)
    try:
        while True:
            c = read_cmd(r)
            if c.op == ProofOp.END:
                break
            vm.step(c)
        vm.finish(require_goal=require_goal)
    except Exception as e:
        raise VMError(f"proof decode/stack error at +{r.i}: {e}")

