#!/usr/bin/env python3
from pathlib import Path
import sys

mode = sys.argv[1]
p = Path("src/util.rs")
s = p.read_text()
old = """    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        if let Some(r) = self.dag.exprs.get(&e) {
            return ExprPtr::local(r)
        }
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }
"""
if mode == "reuse":
    new = """    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        if let Some(r) = self.export_file.dag.exprs.get(&e) {
            return ExprPtr::global(r, r.num_loose_bvars())
        }
        if let Some(r) = self.dag.exprs.get(&e) {
            return ExprPtr::local(r)
        }
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }
"""
elif mode == "probe":
    new = """    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        let _ = self.export_file.dag.exprs.get(&e);
        if let Some(r) = self.dag.exprs.get(&e) {
            return ExprPtr::local(r)
        }
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }
"""
else:
    raise SystemExit(f"unknown mode: {mode}")

if old not in s:
    raise SystemExit("pinned alloc_expr form not found")
p.write_text(s.replace(old, new, 1))
print(f"RGRS global-expression patch applied: {mode}")
