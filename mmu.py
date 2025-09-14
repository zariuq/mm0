import logging
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional

# Simple s-expression parser for MMU files

def _tokenize(text: str):
    tokens: List[str] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        # Line comments start with '--' and run to end of line
        if c == '-' and i + 1 < n and text[i + 1] == '-':
            # Skip the rest of the line
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
            buf = []
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
class Expr:
    kind: str  # 'var' or 'term'
    name: str
    args: Tuple['Expr', ...]
    sort: str

@dataclass
class Term:
    name: str
    args: List[Tuple[str, str]]  # (var, sort)
    ret: str
    def_body: Optional[Expr] = None
    dummy: List[Tuple[str, str]] = field(default_factory=list)

@dataclass
class Thm:
    name: str
    params: List[Tuple[str, str]]  # (var, sort)
    hyps: List[Expr]
    concl: Expr

class MMUVerifier:
    def __init__(self, logger: logging.Logger | None = None):
        self.sorts: Dict[str, None] = {}
        self.terms: Dict[str, Term] = {}
        self.theorems: Dict[str, Thm] = {}
        self.logger = logger or logging.getLogger(__name__)

    # Parsing helpers
    def _parse_params(self, params_ast):
        params = []
        env = {}
        for item in params_ast:
            var, sort = item[0], item[1]
            if sort not in self.sorts:
                raise ValueError(f'unknown sort {sort}')
            params.append((var, sort))
            env[var] = sort
        return params, env

    def _read_expr(self, ast, env):
        if isinstance(ast, str):
            if ast in env:
                return Expr('var', ast, (), env[ast])
            if ast in self.terms and not self.terms[ast].args:
                t = self.terms[ast]
                return Expr('term', ast, (), t.ret)
            raise ValueError(f'unknown symbol {ast}')
        name = ast[0]
        if name not in self.terms:
            raise ValueError(f'unknown term {name}')
        t = self.terms[name]
        if len(ast) - 1 != len(t.args):
            raise ValueError(f'arity mismatch for {name}')
        args = []
        for sub_ast, (_, sort) in zip(ast[1:], t.args):
            e = self._read_expr(sub_ast, env)
            if e.sort != sort:
                raise ValueError(f'sort mismatch in {name}')
            args.append(e)
        return Expr('term', name, tuple(args), t.ret)

    def _instantiate(self, expr: Expr, subst: Dict[str, Expr]):
        if expr.kind == 'var':
            return subst.get(expr.name, expr)
        return Expr('term', expr.name,
                    tuple(self._instantiate(a, subst) for a in expr.args),
                    expr.sort)

    def _eval_proof(self, ast, env, hyps):
        if isinstance(ast, str):
            if ast not in hyps:
                raise ValueError(f'unknown hypothesis {ast}')
            return hyps[ast]
        name = ast[0]
        if name == ':let':
            label = ast[1]
            bound_ast = ast[2]
            bound_val = self._eval_proof(bound_ast, env, hyps)
            hyps[label] = bound_val
            if len(ast) == 4:
                body_ast = ast[3]
                return self._eval_proof(body_ast, env, hyps)
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
        subst = {}
        for (pname, psort), arg_ast in zip(th.params, param_asts):
            arg = self._read_expr(arg_ast, env)
            if arg.sort != psort:
                raise ValueError('parameter sort mismatch')
            subst[pname] = arg
        proof_asts = ast[2:]
        if len(proof_asts) != len(th.hyps):
            raise ValueError('hypothesis count mismatch')
        for p_ast, hyp in zip(proof_asts, th.hyps):
            want = self._instantiate(hyp, subst)
            got = self._eval_proof(p_ast, env, hyps)
            if got != want:
                raise ValueError(
                    f'hypothesis mismatch: expected {want}, got {got}')
        return self._instantiate(th.concl, subst)

    def _eval_conv(self, ast, env, hyps):
        if isinstance(ast, str):
            e = self._read_expr(ast, env)
            return e, e
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
            args = [self._read_expr(a, env) for a in args_ast]
            if len(args) != len(term.args):
                raise ValueError('arity mismatch in unfold')
            if len(dummy_ast) != len(term.dummy):
                raise ValueError('dummy count mismatch in unfold')
            lhs = Expr('term', term_name, tuple(args), term.ret)
            subst = {var: arg for (var, _), arg in zip(term.args, args)}
            for (dvar, dsort), d_ast in zip(term.dummy, dummy_ast):
                d_val = self._read_expr(d_ast, env)
                if d_val.sort != dsort:
                    raise ValueError('dummy sort mismatch in unfold')
                subst[dvar] = d_val
            body = self._instantiate(term.def_body, subst)
            lhs2, rhs2 = self._eval_conv(conv_ast, env, hyps)
            if lhs2 != body:
                raise ValueError('unfold body mismatch')
            return lhs, rhs2
        # general term application
        args = [self._eval_conv(a, env, hyps) for a in ast[1:]]
        lhs_args = [a[0] for a in args]
        rhs_args = [a[1] for a in args]
        if name not in self.terms:
            raise ValueError(f'unknown term {name}')
        t = self.terms[name]
        if len(lhs_args) != len(t.args):
            raise ValueError('arity mismatch in conv')
        return (Expr('term', name, tuple(lhs_args), t.ret),
                Expr('term', name, tuple(rhs_args), t.ret))

    def _handle_sort(self, stmt):
        name = stmt[1]
        self.sorts[name] = None

    def _handle_term(self, stmt):
        name = stmt[1]
        args_ast = stmt[2]
        ret_ast = stmt[3]
        args = []
        for v in args_ast:
            if v[1] not in self.sorts:
                raise ValueError(f'unknown sort {v[1]}')
            args.append((v[0], v[1]))
        ret_sort = ret_ast[0]
        if ret_sort not in self.sorts:
            raise ValueError(f'unknown sort {ret_sort}')
        self.terms[name] = Term(name, args, ret_sort)

    def _handle_def(self, stmt):
        name = stmt[1]
        args_ast = stmt[2]
        ret_ast = stmt[3]
        dummy_ast = stmt[4]
        expr_ast = stmt[5]
        args = []
        for v in args_ast:
            if v[1] not in self.sorts:
                raise ValueError(f'unknown sort {v[1]}')
            args.append((v[0], v[1]))
        ret_sort = ret_ast[0]
        if ret_sort not in self.sorts:
            raise ValueError(f'unknown sort {ret_sort}')
        dummy_params, dummy_env = self._parse_params(dummy_ast)
        term = Term(name, args, ret_sort, dummy=dummy_params)
        self.terms[name] = term
        _, env = self._parse_params(args_ast)
        env.update(dummy_env)
        expr = self._read_expr(expr_ast, env)
        if expr.sort != term.ret:
            raise ValueError('definition sort mismatch')
        term.def_body = expr

    def _handle_axiom(self, stmt):
        name = stmt[1]
        params_ast = stmt[2]
        hyps_ast = stmt[3]
        concl_ast = stmt[4]
        params, env = self._parse_params(params_ast)
        hyps = [self._read_expr(h, env) for h in hyps_ast]
        concl = self._read_expr(concl_ast, env)
        self.theorems[name] = Thm(name, params, hyps, concl)

    def _handle_local(self, stmt):
        kind = stmt[1]
        if kind == 'theorem':
            name = stmt[2]
            params_ast = stmt[3]
            hyps_ast = stmt[4]
            concl_ast = stmt[5]
            dummy_ast = stmt[6]
            proof_ast = stmt[7]
            params, env = self._parse_params(params_ast)
            dummy_params, dummy_env = self._parse_params(dummy_ast)
            env.update(dummy_env)
            hyps = []
            hyp_env = {}
            for h in hyps_ast:
                label, expr_ast = h[0], h[1]
                e = self._read_expr(expr_ast, env)
                hyps.append(e)
                hyp_env[label] = e
            concl = self._read_expr(concl_ast, env)
            res = self._eval_proof(proof_ast, env, hyp_env)
            if res != concl:
                raise ValueError(
                    f'proof of {name} does not match conclusion\n'
                    f'  expected {concl}\n  got {res}')
            self.theorems[name] = Thm(name, params, hyps, concl)
        elif kind == 'def':
            name = stmt[2]
            params_ast = stmt[3]
            ret_ast = stmt[4]
            dummy_ast = stmt[5]
            expr_ast = stmt[6]
            args = []
            for v in params_ast:
                if v[1] not in self.sorts:
                    raise ValueError(f'unknown sort {v[1]}')
                args.append((v[0], v[1]))
            ret_sort = ret_ast[0]
            if ret_sort not in self.sorts:
                raise ValueError(f'unknown sort {ret_sort}')
            dummy_params, dummy_env = self._parse_params(dummy_ast)
            term = Term(name, args, ret_sort, dummy=dummy_params)
            self.terms[name] = term
            _, env = self._parse_params(params_ast)
            env.update(dummy_env)
            expr = self._read_expr(expr_ast, env)
            if expr.sort != term.ret:
                raise ValueError('definition sort mismatch')
            term.def_body = expr
        else:
            self.logger.warning('unknown local statement')

    def _handle_theorem(self, stmt):
        name = stmt[1]
        params_ast = stmt[2]
        hyps_ast = stmt[3]
        concl_ast = stmt[4]
        dummy_ast = stmt[5]
        proof_ast = stmt[6]
        params, env = self._parse_params(params_ast)
        _, dummy_env = self._parse_params(dummy_ast)
        env.update(dummy_env)
        hyps = []
        hyp_env: Dict[str, Expr] = {}
        for h_ast in hyps_ast:
            if isinstance(h_ast, list) and len(h_ast) == 2:
                label, expr_ast = h_ast
            else:
                label, expr_ast = None, h_ast
            h_expr = self._read_expr(expr_ast, env)
            hyps.append(h_expr)
            if label:
                hyp_env[label] = h_expr
        concl = self._read_expr(concl_ast, env)
        res = self._eval_proof(proof_ast, env, hyp_env)
        if res != concl:
            raise ValueError(
                f'proof of {name} does not match conclusion\n'
                f'  expected {concl}\n  got {res}')
        self.theorems[name] = Thm(name, params, hyps, concl)

    def _handle_output(self, stmt):
        pass

    def process(self, stmts):
        for i, stmt in enumerate(stmts, 1):
            head = stmt[0]
            self.logger.debug(f'processing {i}: {head}')
            if head == '-':
                continue
            if head == 'pub':
                if len(stmt) == 2 and isinstance(stmt[1], list):
                    stmt = stmt[1]
                else:
                    stmt = stmt[1:]
                head = stmt[0]
            handler = getattr(self, f'_handle_{head}', None)
            if handler:
                handler(stmt)
            else:
                self.logger.warning(f'unknown statement {head}')


def verify_mmu(path: str, logger: logging.Logger | None = None):
    with open(path, 'r') as f:
        text = f.read()
    stmts = parse_sexpr(text)
    v = MMUVerifier(logger=logger)
    v.process(stmts)
    return v


def verify_mmb(_mm0_path: str, mmb_path: str):
    """Perform basic structural checks on an `.mmb` file.

    This lightweight parser reads the header and table pointers of the
    binary proof file and ensures that all referenced regions are within
    the file bounds. It does **not** attempt full proof checking but
    provides a minimal sanity check without relying on `mm0-c`.
    """
    import struct

    with open(mmb_path, 'rb') as f:
        data = f.read()

    if len(data) < 40:
        raise ValueError('file too small to be an MMB file')

    header = struct.unpack_from('<4sBBHIIIIIIQ', data, 0)
    magic, version, num_sorts, _res, num_terms, num_thms, p_terms, p_thms, \
        p_proof, _res2, p_index = header

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

    # sort table directly follows the header
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



def main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description="Minimal MMU verifier")
    parser.add_argument(
        'files', nargs='+', help='MMU file or MM0 and proof file')
    parser.add_argument('--log-file', dest='log_file', help='write logs to FILE')
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='enable verbose logging')
    args = parser.parse_args(argv)

    log_level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(level=log_level,
                        filename=args.log_file,
                        format='%(message)s')
    logger = logging.getLogger('mmu')
    import os
    if len(args.files) == 1:
        path = args.files[0]
        if path.endswith('.mmu'):
            if os.path.isdir(path):
                parser.error(f'{path} is a directory, expected a file')
            try:
                verify_mmu(path, logger=logger)
            except Exception as e:
                parser.exit(1, f"error: {e}\n")
            print('OK')
            return
        parser.error('expected an .mmu file')
    elif len(args.files) == 2 and args.files[1].endswith('.mmb'):
        mm0_path, mmb_path = args.files
        if os.path.isdir(mmb_path) or os.path.isdir(mm0_path):
            parser.error('expected file paths, not directories')
        try:
            verify_mmb(mm0_path, mmb_path)
        except Exception as e:
            parser.exit(1, f"error: {e}\n")
        print('OK')
        return
    elif len(args.files) == 2:
        _, mmu_path = args.files
        if os.path.isdir(mmu_path):
            parser.error(f'{mmu_path} is a directory, expected a file')
        try:
            verify_mmu(mmu_path, logger=logger)
        except Exception as e:
            parser.exit(1, f"error: {e}\n")
        print('OK')
        return
    else:
        parser.error('expected MMU path or MM0 and MMB paths')


if __name__ == '__main__':
    main()
