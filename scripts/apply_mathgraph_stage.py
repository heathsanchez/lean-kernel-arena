#!/usr/bin/env python3
import sys
from pathlib import Path

stage = sys.argv[1].upper()
assert stage in {"A3", "A4", "A5"}
root = Path('.')

# A3 baseline: larger session budget + E0018.
p = root / 'src/tc.rs'
s = p.read_text()
old = 'const SESSION_BUDGET: usize = 1 << 20;'
assert old in s
p.write_text(s.replace(old, 'const SESSION_BUDGET: usize = 2_621_440;', 1))

p = root / 'src/eval.rs'
s = p.read_text()
old = '''                let Expr::Lambda { body: inner, .. } = self.ctx.read_expr(body) else { break };
                let pruned = self.key_env(env, body);
                env = value::env_extend(self.arena, pruned, args[i]);
                body = inner;
                i += 1;
'''
new = '''                let Expr::Lambda { body: inner, .. } = self.ctx.read_expr(body) else { break };
                env = value::env_extend(self.arena, env, args[i]);
                body = inner;
                i += 1;
'''
assert old in s
s = s.replace(old, new, 1)

# A4 adds E0024: bypass open-eval cache/canonicalization for App only.
if stage in {"A4", "A5"}:
    old = '''        if matches!(
            self.ctx.read_expr_ref(e),
            Expr::App { .. } | Expr::Proj { .. } | Expr::Let { .. } | Expr::Pi { .. } | Expr::Lambda { .. }
        ) {
'''
    new = '''        if matches!(
            self.ctx.read_expr_ref(e),
            Expr::Proj { .. } | Expr::Let { .. } | Expr::Pi { .. } | Expr::Lambda { .. }
        ) {
'''
    assert old in s
    s = s.replace(old, new, 1)

# A5 adds E0025: bypass open-eval cache/canonicalization for Lambda too.
if stage == "A5":
    old = '''        if matches!(
            self.ctx.read_expr_ref(e),
            Expr::Proj { .. } | Expr::Let { .. } | Expr::Pi { .. } | Expr::Lambda { .. }
        ) {
'''
    new = '''        if matches!(
            self.ctx.read_expr_ref(e),
            Expr::Proj { .. } | Expr::Let { .. } | Expr::Pi { .. }
        ) {
'''
    assert old in s
    s = s.replace(old, new, 1)

p.write_text(s)
print(f'Applied MathGraph {stage}')
