"""Minimal equality kernel used by the MMB verifier."""
from __future__ import annotations

from typing import Iterable

from .ast import Expr, Term


def refl(e: Expr) -> tuple[Expr, Expr]:
    return e, e


def sym(c: tuple[Expr, Expr]) -> tuple[Expr, Expr]:
    lhs, rhs = c
    return rhs, lhs


def trans(c1: tuple[Expr, Expr], c2: tuple[Expr, Expr]) -> tuple[Expr, Expr]:
    l1, r1 = c1
    l2, r2 = c2
    if r1 != l2:
        raise ValueError('trans mismatch')
    return l1, r2


def cong(head: Expr, args: Iterable[tuple[Expr, Expr]]) -> tuple[Expr, Expr]:
    """Congruence for application."""
    lhs_args = []
    rhs_args = []
    for l, r in args:
        lhs_args.append(l)
        rhs_args.append(r)
    lhs = Expr('app', head.index, tuple(lhs_args), head.sort)
    rhs = Expr('app', head.index, tuple(rhs_args), head.sort)
    return lhs, rhs


def unfold(term: Term, args: Iterable[Expr]) -> tuple[Expr, Expr]:
    if term.def_body is None:
        raise ValueError('term has no definition to unfold')
    subst = {i: a for i, a in enumerate(args)}
    body = _instantiate(term.def_body, subst)
    lhs = Expr('app', term_index(term), tuple(args), term.ret)
    return lhs, body


def _instantiate(expr: Expr, subst: dict[int, Expr]) -> Expr:
    if expr.kind in ('var', 'dummy'):
        return subst.get(expr.index, expr)
    return Expr('app', expr.index,
                tuple(_instantiate(a, subst) for a in expr.args),
                expr.sort)


def term_index(term: Term) -> int:
    raise NotImplementedError
