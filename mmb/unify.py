"""Decode-only unify VM to materialize expressions.

This follows the tiny interpreter described in the milestone: it supports
TERM(/SAVE), REF, DUMMY, HYP and END opcodes. The VM builds `Expr` values
using external arity information for TERM instructions. It is intentionally
minimal – convertibility and full sort checking are deferred.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, List

from .ast import Expr
from .cmd import UnifyOp, read_cmd
from .io import BR


@dataclass
class UnifyResult:
    """Result of running a unify program.

    For theorems/axioms the stack ends with ``hyps + concl``; for terms
    (definitions) there is only the resulting expression.
    """

    params: List[Expr]
    hyps: List[Expr]
    concl: Expr
    def_body: Expr | None = None


class UnifyVM:
    """Build expressions from a unify stream."""

    def __init__(self, arity_of_term: Callable[[int], int]):
        self.arity_of_term = arity_of_term
        self.stack: List[Expr] = []
        self.saved: List[Expr] = []

    # --- stack helpers -------------------------------------------------
    def _push(self, e: Expr) -> None:
        self.stack.append(e)

    def _pop(self, n: int) -> List[Expr]:
        if n > len(self.stack):
            raise ValueError("unify underflow")
        res = self.stack[-n:]
        del self.stack[-n:]
        return res

    # --- execution -----------------------------------------------------
    def step(self, op: int, data: int) -> None:
        if op in (UnifyOp.TERM, UnifyOp.TERM_SAVE):
            n = self.arity_of_term(data)
            args = self._pop(n)
            e = Expr("app", data, tuple(args), 0)
            self._push(e)
            if op == UnifyOp.TERM_SAVE:
                self.saved.append(e)
        elif op == UnifyOp.REF:
            try:
                self._push(self.saved[data])
            except IndexError:  # pragma: no cover - exercised in tests
                raise ValueError("ref oob")
        elif op == UnifyOp.DUMMY:
            self._push(Expr("dummy", len(self.saved), (), data))
        elif op == UnifyOp.HYP:
            self._push(Expr("var", -1, (), 0))
        elif op == UnifyOp.END:
            return
        else:  # pragma: no cover - defensive
            raise ValueError(f"unsupported unify opcode {op:#x}")


def run_unify(
    buf: memoryview,
    arity_of_term: Callable[[int], int],
    *,
    outputs: int,
    initial: List[Expr] | None = None,
) -> List[Expr]:
    """Execute a unify program returning the top ``outputs`` expressions.

    ``arity_of_term`` supplies arities for TERM instructions. ``outputs`` is
    the number of expressions expected on the stack at the end (hyps then
    concl). ``initial`` seeds the VM stack before execution. Raises
    ``ValueError`` on stack underflow or malformed streams.
    """

    vm = UnifyVM(arity_of_term)
    if initial:
        vm.stack.extend(initial)
    r = BR(buf)
    while True:
        c = read_cmd(r)
        if c.op == UnifyOp.END:
            break
        vm.step(c.op, c.data)
    if len(vm.stack) < outputs:
        raise ValueError("unify underflow")
    return vm.stack[-outputs:]
