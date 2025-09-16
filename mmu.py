import logging
from dataclasses import dataclass
from typing import Dict, Iterable, List, Mapping, MutableMapping, Optional, Sequence, Tuple


# Simple s-expression parser for MMU files


def _tokenize(text: str) -> List[str]:
    tokens: List[str] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c == '-' and i + 1 < n and text[i + 1] == '-':
            while i < n and text[i] != '\n':
                i += 1
            continue
        if c.isspace():
            i += 1
            continue
        if c in '()':
            tokens.append(c)
            i += 1
            continue
        if c == '"':
            j = i + 1
            buf: List[str] = []
            while j < n:
                if text[j] == '"' and text[j - 1] != '\\':
                    break
                buf.append(text[j])
                j += 1
            tokens.append('"' + ''.join(buf) + '"')
            i = j + 1
            continue
        j = i
        while j < n and not text[j].isspace() and text[j] not in '()':
            j += 1
        tokens.append(text[i:j])
        i = j
    return tokens


def parse_sexpr(text: str):
    tokens = _tokenize(text)
    stack: List[List] = [[]]
    for tok in tokens:
        if tok == '(':
            stack.append([])
        elif tok == ')':
            if len(stack) == 1:
                raise ValueError('unmatched )')
            last = stack.pop()
            stack[-1].append(last)
        else:
            if tok.startswith('"') and tok.endswith('"'):
                tok = tok[1:-1]
            stack[-1].append(tok)
    if len(stack) != 1:
        raise ValueError('unmatched (')
    return stack[0]


@dataclass(frozen=True)
class SortInfo:
    name: str
    strict: bool
    provable: bool


@dataclass(frozen=True)
class TypeAnnot:
    sort: str
    deps: Tuple[int, ...]


@dataclass(frozen=True)
class TermSig:
    name: str
    args: Tuple[TypeAnnot, ...]
    ret: TypeAnnot


@dataclass(frozen=True)
class Expr:
    kind: str  # 'var' | 'dummy' | 'app'
    sym: Optional[str]
    args: Tuple['Expr', ...]
    sort: str
    free_dummies: frozenset[int]


@dataclass(frozen=True)
class VarInfo:
    sort: str
    kind: str  # 'param' | 'dummy'
    dummy_id: Optional[int]


@dataclass(frozen=True)
class BinderDecl:
    name: str
    annot: TypeAnnot
    kind: str  # 'param' | 'dummy'
    index: int
    dummy_id: Optional[int]


@dataclass
class TermDecl:
    name: str
    sig: TermSig
    args: Tuple[BinderDecl, ...]
    dummies: Tuple[BinderDecl, ...]
    def_body: Optional[Expr] = None


@dataclass
class TheoremDecl:
    name: str
    params: Tuple[BinderDecl, ...]
    hyps: Tuple[Expr, ...]
    concl: Expr


class MMUVerifier:
    def __init__(self, logger: Optional[logging.Logger] = None):
        self.sorts: Dict[str, SortInfo] = {}
        self.terms: Dict[str, TermDecl] = {}
        self.theorems: Dict[str, TheoremDecl] = {}
        self._next_dummy_id = 0
        self.logger = logger or logging.getLogger(__name__)

    # ------------------------------------------------------------------
    # Binder helpers

    def _fresh_dummy_id(self) -> int:
        dummy = self._next_dummy_id
        self._next_dummy_id += 1
        return dummy

    def _lookup_sort(self, sort: str) -> SortInfo:
        if sort not in self.sorts:
            raise ValueError(f'unknown sort {sort}')
        return self.sorts[sort]

    def _make_type_annotation(
        self,
        sort: str,
        deps_ast: Sequence,
        binders: Sequence[BinderDecl],
        binder_env: Mapping[str, BinderDecl],
    ) -> TypeAnnot:
        self._lookup_sort(sort)
        if not deps_ast:
            return TypeAnnot(sort, ())
        dep_indices: List[int] = []
        for dep in deps_ast:
            if dep not in binder_env:
                raise ValueError(f'unknown dependency {dep}')
            binder = binder_env[dep]
            dep_indices.append(binder.index)
        return TypeAnnot(sort, tuple(dep_indices))

    def _parse_single_binder(
        self,
        entry: Sequence,
        binders: List[BinderDecl],
        binder_env: MutableMapping[str, BinderDecl],
        *,
        allow_param: bool = True,
        allow_dummy: bool = True,
        len2_kind: str = 'dummy',
    ) -> BinderDecl:
        if not entry:
            raise ValueError('invalid binder entry')
        if len(entry) == 2:
            if not allow_dummy:
                raise ValueError('unexpected dummy binder')
            name, sort = entry
            if name in binder_env:
                if name.startswith('_'):
                    name = f'{name}{len(binders)}'
                else:
                    raise ValueError(f'duplicate variable {name}')
            if len2_kind == 'dummy':
                binder = BinderDecl(
                    name=name,
                    annot=TypeAnnot(sort, ()),
                    kind='dummy',
                    index=len(binders),
                    dummy_id=self._fresh_dummy_id(),
                )
            else:
                binder = BinderDecl(
                    name=name,
                    annot=TypeAnnot(sort, ()),
                    kind='param',
                    index=len(binders),
                    dummy_id=None,
                )
        elif len(entry) == 3:
            if not allow_param:
                raise ValueError('unexpected parameter binder')
            name, sort, deps_ast = entry
            if name in binder_env:
                if name.startswith('_'):
                    name = f'{name}{len(binders)}'
                else:
                    raise ValueError(f'duplicate variable {name}')
            annot = self._make_type_annotation(sort, deps_ast, binders, binder_env)
            binder = BinderDecl(
                name=name,
                annot=annot,
                kind='param',
                index=len(binders),
                dummy_id=None,
            )
        else:
            raise ValueError('invalid binder entry')
        return binder

    def _parse_binders(
        self,
        binder_asts: Sequence[Sequence],
        binders: List[BinderDecl],
        binder_env: MutableMapping[str, BinderDecl],
        *,
        allow_param: bool = True,
        allow_dummy: bool = True,
        len2_kind: str = 'dummy',
    ) -> Tuple[BinderDecl, ...]:
        result: List[BinderDecl] = []
        for entry in binder_asts:
            binder = self._parse_single_binder(
                entry,
                binders,
                binder_env,
                allow_param=allow_param,
                allow_dummy=allow_dummy,
                len2_kind=len2_kind,
            )
            binders.append(binder)
            binder_env[binder.name] = binder
            result.append(binder)
        return tuple(result)

    def _varinfo_from_binder(self, binder: BinderDecl) -> VarInfo:
        if binder.kind == 'dummy':
            return VarInfo(binder.annot.sort, 'dummy', binder.dummy_id)
        return VarInfo(binder.annot.sort, 'param', None)

    # ------------------------------------------------------------------
    # Expression helpers

    def _allowed_from_deps(
        self,
        deps: Tuple[int, ...],
        binders: Sequence[BinderDecl],
        dummy_sets: Mapping[int, frozenset[int]],
    ) -> frozenset[int]:
        if not deps:
            return frozenset()
        allowed: set[int] = set()
        for idx in deps:
            if idx < 0 or idx >= len(binders):
                raise ValueError('dependency index out of range')
            binder = binders[idx]
            if idx not in dummy_sets:
                raise ValueError('dependency binder has no instantiation')
            allowed |= dummy_sets[idx]
        return frozenset(allowed)

    def _initial_dummy_sets(self, binders: Sequence[BinderDecl]) -> Dict[int, frozenset[int]]:
        dummy_sets: Dict[int, frozenset[int]] = {}
        for binder in binders:
            if binder.kind == 'dummy':
                if binder.dummy_id is None:
                    raise ValueError('missing dummy id')
                dummy_sets[binder.index] = frozenset({binder.dummy_id})
            else:
                dummy_sets[binder.index] = frozenset()
        return dummy_sets

    def _read_expr(self, ast, env: Mapping[str, VarInfo]) -> Expr:
        if isinstance(ast, str):
            if ast in env:
                info = env[ast]
                if info.kind == 'dummy':
                    if info.dummy_id is None:
                        raise ValueError('internal error: missing dummy id')
                    return Expr('dummy', ast, (), info.sort, frozenset({info.dummy_id}))
                return Expr('var', ast, (), info.sort, frozenset())
            if ast in self.terms:
                term = self.terms[ast]
                if term.sig.args:
                    raise ValueError(f'arity mismatch for {ast}')
                expr, _ = self._analyze_app(ast, [])
                return expr
            raise ValueError(f'unknown symbol {ast}')
        if not ast:
            raise ValueError('empty expression')
        name = ast[0]
        arg_exprs = [self._read_expr(sub_ast, env) for sub_ast in ast[1:]]
        expr, _ = self._analyze_app(name, arg_exprs)
        return expr

    def _analyze_app(
        self, name: str, args: Sequence[Expr]
    ) -> Tuple[Expr, Dict[int, frozenset[int]]]:
        if name not in self.terms:
            raise ValueError(f'unknown term {name}')
        term = self.terms[name]
        if len(args) != len(term.args):
            raise ValueError(f'arity mismatch for {name}')
        dummy_sets: Dict[int, frozenset[int]] = {}
        result_free: set[int] = set()
        for binder, arg_expr in zip(term.args, args):
            if arg_expr.sort != binder.annot.sort:
                raise ValueError(f'sort mismatch in {name}')
            allowed = self._allowed_from_deps(binder.annot.deps, term.args, dummy_sets)
            sort_info = self._lookup_sort(arg_expr.sort)
            if sort_info.strict and binder.kind == 'dummy':
                if not arg_expr.free_dummies.issubset(allowed):
                    raise ValueError('strict dependency violation in argument')
            dummy_sets[binder.index] = arg_expr.free_dummies
            if binder.kind != 'dummy':
                result_free |= arg_expr.free_dummies
        for binder in term.args:
            if binder.kind == 'dummy':
                result_free -= dummy_sets.get(binder.index, frozenset())
        sort_info = self._lookup_sort(term.sig.ret.sort)
        allowed_ret = set(self._allowed_from_deps(term.sig.ret.deps, term.args, dummy_sets))
        for binder in term.args:
            if binder.kind != 'dummy':
                allowed_ret |= set(dummy_sets.get(binder.index, frozenset()))
        if sort_info.strict and not result_free.issubset(allowed_ret):
            raise ValueError('strict dependency violation in result')
        expr = Expr('app', name, tuple(args), term.sig.ret.sort, frozenset(result_free))
        return expr, dummy_sets

    def _instantiate(self, expr: Expr, subst: Mapping[str, Expr]) -> Expr:
        if expr.kind in {'var', 'dummy'}:
            if expr.sym in subst:
                return subst[expr.sym]
            return expr
        if expr.kind != 'app':
            raise ValueError('unknown expression kind')
        args = [self._instantiate(a, subst) for a in expr.args]
        return self._build_app(expr.sym, args)

    def _build_app(self, name: str, args: Sequence[Expr]) -> Expr:
        expr, _ = self._analyze_app(name, args)
        return expr

    # ------------------------------------------------------------------
    # Proof helpers

    def _eval_conv(self, ast, env: Mapping[str, VarInfo], hyps: Mapping[str, Expr]) -> Tuple[Expr, Expr]:
        if isinstance(ast, str):
            e = self._read_expr(ast, env)
            return e, e
        if not ast:
            raise ValueError('empty conversion expression')
        name = ast[0]
        if name == ':refl':
            if len(ast) != 2:
                raise ValueError('invalid :refl')
            e = self._read_expr(ast[1], env)
            return e, e
        if name == ':sym':
            lhs, rhs = self._eval_conv(ast[1], env, hyps)
            return rhs, lhs
        if name == ':trans':
            lhs1, rhs1 = self._eval_conv(ast[1], env, hyps)
            lhs2, rhs2 = self._eval_conv(ast[2], env, hyps)
            if rhs1 != lhs2:
                raise ValueError('trans mismatch')
            return lhs1, rhs2
        if name == ':unfold':
            if len(ast) != 5:
                raise ValueError('invalid :unfold')
            term_name = ast[1]
            args_ast = ast[2]
            dummy_ast = ast[3]
            conv_ast = ast[4]
            if term_name not in self.terms:
                raise ValueError(f'unknown term {term_name}')
            term = self.terms[term_name]
            if term.def_body is None:
                raise ValueError('cannot unfold non-definition')
            args = [self._read_expr(arg, env) for arg in args_ast]
            lhs, dummy_sets = self._analyze_app(term_name, args)
            binders = list(term.args)
            binder_env = {binder.name: binder for binder in binders}
            dummy_exprs: List[Expr] = []
            if len(dummy_ast) != len(term.dummies):
                raise ValueError('dummy count mismatch in unfold')
            for binder, ast_expr in zip(term.dummies, dummy_ast):
                binders.append(binder)
                binder_env[binder.name] = binder
                expr = self._read_expr(ast_expr, env)
                if expr.sort != binder.annot.sort:
                    raise ValueError('dummy sort mismatch in unfold')
                allowed = self._allowed_from_deps(
                    binder.annot.deps, binders, dummy_sets
                )
                sort_info = self._lookup_sort(expr.sort)
                if sort_info.strict and not expr.free_dummies.issubset(allowed):
                    raise ValueError('dummy dependency violation in unfold')
                dummy_sets[binder.index] = expr.free_dummies
                dummy_exprs.append(expr)
            subst: Dict[str, Expr] = {}
            for binder, arg_expr in zip(term.args, args):
                subst[binder.name] = arg_expr
            for binder, expr in zip(term.dummies, dummy_exprs):
                subst[binder.name] = expr
            body = self._instantiate(term.def_body, subst)
            lhs_conv, rhs_conv = self._eval_conv(conv_ast, env, hyps)
            if lhs_conv != body:
                raise ValueError('unfold body mismatch')
            return lhs, rhs_conv
        arg_pairs = [self._eval_conv(a, env, hyps) for a in ast[1:]]
        lhs_args = [p[0] for p in arg_pairs]
        rhs_args = [p[1] for p in arg_pairs]
        lhs, _ = self._analyze_app(name, lhs_args)
        rhs, _ = self._analyze_app(name, rhs_args)
        return lhs, rhs

    def _eval_proof(
        self,
        ast,
        env: MutableMapping[str, VarInfo],
        hyps: MutableMapping[str, Expr],
    ) -> Expr:
        if isinstance(ast, str):
            if ast not in hyps:
                raise ValueError(f'unknown hypothesis {ast}')
            return hyps[ast]
        if not ast:
            raise ValueError('empty proof expression')
        name = ast[0]
        if name == ':let':
            label = ast[1]
            bound_val = self._eval_proof(ast[2], env, hyps)
            if label in hyps:
                raise ValueError(f'shadowed hypothesis {label}')
            hyps[label] = bound_val
            if len(ast) == 4:
                return self._eval_proof(ast[3], env, hyps)
            return bound_val
        if name == ':conv':
            goal_ast, conv_ast, proof_ast = ast[1], ast[2], ast[3]
            goal = self._read_expr(goal_ast, env)
            lhs, rhs = self._eval_conv(conv_ast, env, hyps)
            if lhs != goal:
                raise ValueError('conversion goal mismatch')
            proof_res = self._eval_proof(proof_ast, env, hyps)
            if proof_res != rhs:
                raise ValueError('conversion proof mismatch')
            return goal
        if name not in self.theorems:
            raise ValueError(f'unknown theorem {name}')
        th = self.theorems[name]
        param_asts = ast[1]
        if len(param_asts) != len(th.params):
            raise ValueError('parameter count mismatch')
        subst: Dict[str, Expr] = {}
        dummy_sets: Dict[int, frozenset[int]] = {}
        for binder, arg_ast in zip(th.params, param_asts):
            arg_expr = self._read_expr(arg_ast, env)
            if arg_expr.sort != binder.annot.sort:
                raise ValueError('parameter sort mismatch')
            allowed = self._allowed_from_deps(
                binder.annot.deps, th.params, dummy_sets
            )
            sort_info = self._lookup_sort(arg_expr.sort)
            if sort_info.strict and binder.kind == 'dummy':
                if not arg_expr.free_dummies.issubset(allowed):
                    raise ValueError('strict dependency violation in parameter')
            dummy_sets[binder.index] = arg_expr.free_dummies
            subst[binder.name] = arg_expr
        proof_asts = ast[2:]
        if len(proof_asts) != len(th.hyps):
            raise ValueError('hypothesis count mismatch')
        for p_ast, hyp in zip(proof_asts, th.hyps):
            want = self._instantiate(hyp, subst)
            got = self._eval_proof(p_ast, env, hyps)
            if got != want:
                raise ValueError('hypothesis mismatch')
        return self._instantiate(th.concl, subst)

    # ------------------------------------------------------------------
    # Statement handlers

    def _handle_sort(self, stmt: Sequence) -> None:
        name = stmt[1]
        flags = set(stmt[2:])
        strict = 'strict' in flags
        provable = 'provable' in flags
        self.sorts[name] = SortInfo(name, strict, provable)

    def _handle_term(self, stmt: Sequence) -> None:
        name = stmt[1]
        args_ast = stmt[2]
        ret_ast = stmt[3]
        binders: List[BinderDecl] = []
        binder_env: Dict[str, BinderDecl] = {}
        args = self._parse_binders(args_ast, binders, binder_env)
        ret_sort = ret_ast[0]
        ret_deps_ast = ret_ast[1] if len(ret_ast) > 1 else []
        ret_annot = self._make_type_annotation(ret_sort, ret_deps_ast, binders, binder_env)
        sig = TermSig(name, tuple(b.annot for b in args), ret_annot)
        self.terms[name] = TermDecl(name, sig, tuple(args), (), None)

    def _handle_def(self, stmt: Sequence) -> None:
        name = stmt[1]
        args_ast = stmt[2]
        ret_ast = stmt[3]
        dummy_ast = stmt[4]
        expr_ast = stmt[5]
        binders: List[BinderDecl] = []
        binder_env: Dict[str, BinderDecl] = {}
        args = self._parse_binders(args_ast, binders, binder_env)
        ret_sort = ret_ast[0]
        ret_deps_ast = ret_ast[1] if len(ret_ast) > 1 else []
        ret_annot = self._make_type_annotation(ret_sort, ret_deps_ast, binders, binder_env)
        dummy_binders = self._parse_binders(dummy_ast, binders, binder_env, allow_param=False)
        all_binders = tuple(binders)
        expr_env = {binder.name: self._varinfo_from_binder(binder) for binder in all_binders}
        expr = self._read_expr(expr_ast, expr_env)
        if expr.sort != ret_sort:
            raise ValueError('definition sort mismatch')
        sort_info = self._lookup_sort(ret_sort)
        if sort_info.strict:
            dummy_sets = self._initial_dummy_sets(all_binders)
            allowed = self._allowed_from_deps(ret_annot.deps, args, dummy_sets)
            if not expr.free_dummies.issubset(allowed):
                raise ValueError('definition dummy escape')
        sig = TermSig(name, tuple(b.annot for b in args), ret_annot)
        self.terms[name] = TermDecl(name, sig, tuple(args), tuple(dummy_binders), expr)

    def _handle_axiom(self, stmt: Sequence) -> None:
        name = stmt[1]
        params_ast = stmt[2]
        hyps_ast = stmt[3]
        concl_ast = stmt[4]
        binders: List[BinderDecl] = []
        binder_env: Dict[str, BinderDecl] = {}
        params = self._parse_binders(params_ast, binders, binder_env)
        expr_env = {binder.name: self._varinfo_from_binder(binder) for binder in params}
        hyps: List[Expr] = []
        for hyp_ast in hyps_ast:
            expr = self._read_expr(hyp_ast, expr_env)
            sort_info = self._lookup_sort(expr.sort)
            if not sort_info.provable:
                raise ValueError('hypothesis in non-provable sort')
            hyps.append(expr)
        concl = self._read_expr(concl_ast, expr_env)
        concl_info = self._lookup_sort(concl.sort)
        if not concl_info.provable:
            raise ValueError('conclusion in non-provable sort')
        # Conclusions may contain free variables of non-strict sorts.
        self.theorems[name] = TheoremDecl(name, tuple(params), tuple(hyps), concl)

    def _handle_local(self, stmt: Sequence) -> None:
        kind = stmt[1]
        if kind == 'theorem':
            name = stmt[2]
            params_ast = stmt[3]
            hyps_ast = stmt[4]
            concl_ast = stmt[5]
            dummy_ast = stmt[6]
            proof_ast = stmt[7]
            binders: List[BinderDecl] = []
            binder_env: Dict[str, BinderDecl] = {}
            params = self._parse_binders(params_ast, binders, binder_env)
            self._parse_binders(dummy_ast, binders, binder_env, allow_param=False)
            expr_env = {
                binder.name: self._varinfo_from_binder(binder)
                for binder in binders
            }
            hyps: List[Expr] = []
            hyp_env: Dict[str, Expr] = {}
            for hyp_entry in hyps_ast:
                if isinstance(hyp_entry, list) and len(hyp_entry) == 2:
                    label, expr_ast = hyp_entry
                else:
                    label, expr_ast = None, hyp_entry
                expr = self._read_expr(expr_ast, expr_env)
                hyp_info = self._lookup_sort(expr.sort)
                if not hyp_info.provable:
                    raise ValueError('hypothesis in non-provable sort')
                hyps.append(expr)
                if label:
                    if label in hyp_env:
                        raise ValueError(f'duplicate hypothesis label {label}')
                    hyp_env[label] = expr
            concl = self._read_expr(concl_ast, expr_env)
            concl_info = self._lookup_sort(concl.sort)
            if not concl_info.provable:
                raise ValueError('conclusion in non-provable sort')
            proof = self._eval_proof(proof_ast, dict(expr_env), dict(hyp_env))
            if proof != concl:
                raise ValueError(
                    f'proof of {name} does not match conclusion\n'
                    f'  expected {concl}\n  got {proof}'
                )
            self.theorems[name] = TheoremDecl(name, tuple(params), tuple(hyps), concl)
        elif kind == 'def':
            name = stmt[2]
            params_ast = stmt[3]
            ret_ast = stmt[4]
            dummy_ast = stmt[5]
            expr_ast = stmt[6]
            self._handle_def(['def', name, params_ast, ret_ast, dummy_ast, expr_ast])
        else:
            self.logger.warning('unknown local statement')

    def _handle_theorem(self, stmt: Sequence) -> None:
        name = stmt[1]
        params_ast = stmt[2]
        hyps_ast = stmt[3]
        concl_ast = stmt[4]
        dummy_ast = stmt[5]
        proof_ast = stmt[6]
        binders: List[BinderDecl] = []
        binder_env: Dict[str, BinderDecl] = {}
        params = self._parse_binders(params_ast, binders, binder_env)
        self._parse_binders(dummy_ast, binders, binder_env, allow_param=False)
        expr_env = {binder.name: self._varinfo_from_binder(binder) for binder in binders}
        hyps: List[Expr] = []
        hyp_env: Dict[str, Expr] = {}
        for entry in hyps_ast:
            if isinstance(entry, list) and len(entry) == 2:
                label, expr_ast = entry
            else:
                label, expr_ast = None, entry
            expr = self._read_expr(expr_ast, expr_env)
            hyp_info = self._lookup_sort(expr.sort)
            if not hyp_info.provable:
                raise ValueError('hypothesis in non-provable sort')
            hyps.append(expr)
            if label:
                if label in hyp_env:
                    raise ValueError(f'duplicate hypothesis label {label}')
                hyp_env[label] = expr
        concl = self._read_expr(concl_ast, expr_env)
        concl_info = self._lookup_sort(concl.sort)
        if not concl_info.provable:
            raise ValueError('conclusion in non-provable sort')
        result = self._eval_proof(proof_ast, dict(expr_env), dict(hyp_env))
        if result != concl:
            raise ValueError(
                f'proof of {name} does not match conclusion\n'
                f'  expected {concl}\n  got {result}'
            )
        self.theorems[name] = TheoremDecl(name, tuple(params), tuple(hyps), concl)

    def _handle_output(self, stmt: Sequence) -> None:  # noqa: D401
        """Outputs are ignored by the verifier."""

    def process(self, stmts: Sequence[Sequence]) -> None:
        for i, stmt in enumerate(stmts, 1):
            if not stmt:
                continue
            head = stmt[0]
            self.logger.debug('processing %d: %s', i, head)
            if head == '-':
                continue
            if head == 'pub':
                if len(stmt) == 2 and isinstance(stmt[1], list):
                    stmt = stmt[1]
                else:
                    stmt = stmt[1:]
                head = stmt[0]
            handler = getattr(self, f'_handle_{head}', None)
            if handler is None:
                self.logger.warning('unknown statement %s', head)
                continue
            handler(stmt)


def verify_mmu(path: str, logger: Optional[logging.Logger] = None) -> MMUVerifier:
    with open(path, 'r') as f:
        text = f.read()
    stmts = parse_sexpr(text)
    verifier = MMUVerifier(logger=logger)
    verifier.process(stmts)
    return verifier


def verify_mmb(_mm0_path: str, mmb_path: str) -> None:
    """Perform basic structural checks on an `.mmb` file."""
    import struct

    with open(mmb_path, 'rb') as f:
        data = f.read()

    if len(data) < 40:
        raise ValueError('file too small to be an MMB file')

    header = struct.unpack_from('<4sBBHIIIIIIQ', data, 0)
    magic, version, num_sorts, _res, num_terms, num_thms, p_terms, p_thms, p_proof, _res2, p_index = header

    if magic != b'MM0B':
        raise ValueError('missing MM0B header')
    if version != 1:
        raise ValueError(f'unsupported MMB version {version}')

    size = len(data)

    def check_ptr(ptr: int, align: int = 1) -> None:
        if ptr % align:
            raise ValueError('misaligned pointer')
        if ptr > size:
            raise ValueError('pointer out of range')

    if 40 + num_sorts > size:
        raise ValueError('sort table exceeds file size')

    check_ptr(p_terms, 8)
    if p_terms + num_terms * 8 > size:
        raise ValueError('term table exceeds file size')

    check_ptr(p_thms, 8)
    if p_thms + num_thms * 8 > size:
        raise ValueError('theorem table exceeds file size')

    check_ptr(p_proof)
    if p_index:
        check_ptr(p_index, 8)


def main(argv: Optional[Sequence[str]] = None) -> None:
    import argparse
    import os

    parser = argparse.ArgumentParser(description='Minimal MMU verifier')
    parser.add_argument('files', nargs='+', help='MMU file or MM0 and proof file')
    parser.add_argument('--log-file', dest='log_file', help='write logs to FILE')
    parser.add_argument('-v', '--verbose', action='store_true', help='enable verbose logging')
    args = parser.parse_args(argv)

    log_level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(
        level=log_level,
        filename=args.log_file,
        format='%(message)s',
    )
    logger = logging.getLogger('mmu')

    if len(args.files) == 1:
        path = args.files[0]
        if path.endswith('.mmu'):
            if os.path.isdir(path):
                parser.error(f'{path} is a directory, expected a file')
            try:
                verify_mmu(path, logger=logger)
            except Exception as e:  # noqa: BLE001
                parser.exit(1, f'error: {e}\n')
            print('OK')
            return
        parser.error('expected an .mmu file')
    elif len(args.files) == 2 and args.files[1].endswith('.mmb'):
        mm0_path, mmb_path = args.files
        if os.path.isdir(mmb_path) or os.path.isdir(mm0_path):
            parser.error('expected file paths, not directories')
        try:
            verify_mmb(mm0_path, mmb_path)
        except Exception as e:  # noqa: BLE001
            parser.exit(1, f'error: {e}\n')
        print('OK')
        return
    elif len(args.files) == 2:
        _, mmu_path = args.files
        if os.path.isdir(mmu_path):
            parser.error(f'{mmu_path} is a directory, expected a file')
        try:
            verify_mmu(mmu_path, logger=logger)
        except Exception as e:  # noqa: BLE001
            parser.exit(1, f'error: {e}\n')
        print('OK')
        return
    else:
        parser.error('expected MMU path or MM0 and MMB paths')


if __name__ == '__main__':
    main()
