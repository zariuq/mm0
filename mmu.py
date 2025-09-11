import logging
from dataclasses import dataclass
from typing import List, Tuple, Dict

# Simple s-expression parser for MMU files

def _tokenize(text: str):
    tokens: List[str] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
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
        if name == ':sym':
            lhs, rhs = self._eval_conv(ast[1], env, hyps)
            return rhs, lhs
        if name == ':unfold':
            term_name = ast[1]
            args_ast = ast[2]
            body_ast = ast[4]
            args_lhs = [self._read_expr(a, env) for a in args_ast]
            lhs = Expr('term', term_name, tuple(args_lhs), self.terms[term_name].ret)
            _lhs, body = self._eval_conv(body_ast, env, hyps)
            return lhs, body
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
        args = [(v[0], v[1]) for v in args_ast]
        self.terms[name] = Term(name, args, ret_ast[0])

    def _handle_def(self, stmt):
        name = stmt[1]
        args_ast = stmt[2]
        ret_ast = stmt[3]
        dummy_ast = stmt[4]
        expr_ast = stmt[5]
        args = [(v[0], v[1]) for v in args_ast]
        term = Term(name, args, ret_ast[0])
        self.terms[name] = term
        _, env = self._parse_params(args_ast)
        _, dummy_env = self._parse_params(dummy_ast)
        env.update(dummy_env)
        expr = self._read_expr(expr_ast, env)
        if expr.sort != term.ret:
            raise ValueError('definition sort mismatch')

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
            args = [(v[0], v[1]) for v in params_ast]
            term = Term(name, args, ret_ast[0])
            self.terms[name] = term
            _, env = self._parse_params(params_ast)
            _, dummy_env = self._parse_params(dummy_ast)
            env.update(dummy_env)
            expr = self._read_expr(expr_ast, env)
            if expr.sort != term.ret:
                raise ValueError('definition sort mismatch')
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
        hyps = [self._read_expr(h, env) for h in hyps_ast]
        concl = self._read_expr(concl_ast, env)
        hyp_env = {}
        for h_expr, h_ast in zip(hyps, hyps_ast):
            label = h_ast[0] if isinstance(h_ast, list) and len(h_ast) == 2 else None
            if label:
                hyp_env[label] = h_expr
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


def main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description="Minimal MMU verifier")
    parser.add_argument(
        'files', nargs='+', help='MMU file or MM0 and MMU file')
    parser.add_argument('--log-file', dest='log_file', help='write logs to FILE')
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='enable verbose logging')
    args = parser.parse_args(argv)

    log_level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(level=log_level,
                        filename=args.log_file,
                        format='%(message)s')
    logger = logging.getLogger('mmu')
    if len(args.files) == 1:
        mmu_path = args.files[0]
    elif len(args.files) == 2:
        # Allow users to supply an MM0 file followed by the MMU file
        mmu_path = args.files[1]
    else:
        parser.error('expected MMU path or MM0 and MMU paths')
    import os
    if os.path.isdir(mmu_path):
        parser.error(f'{mmu_path} is a directory, expected a file')
    try:
        verify_mmu(mmu_path, logger=logger)
    except Exception as e:
        parser.exit(1, f"error: {e}\n")
    print('OK')


if __name__ == '__main__':
    main()