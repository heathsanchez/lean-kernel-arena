#!/usr/bin/env python3
from pathlib import Path

u = Path('src/util.rs')
s = u.read_text()
marker = "// RGRS_EXPR_STATS\n"
if marker in s:
    raise SystemExit('RGRS instrumentation already present')

stats = r'''// RGRS_EXPR_STATS
pub static RGRS_EXPR_PROBES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static RGRS_EXPR_GLOBAL_HITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static RGRS_EXPR_GLOBAL_HIT_LOCAL_HITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static RGRS_EXPR_GLOBAL_HIT_LOCAL_MISSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static RGRS_EXPR_LOCAL_HITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static RGRS_EXPR_LOCAL_INSERTS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

pub fn rgrs_dump_expr_stats() {
    use std::sync::atomic::Ordering::Relaxed;
    eprintln!(
        "RGRS_EXPR_STATS probes={} global_hits={} global_hit_local_hits={} global_hit_local_misses={} local_hits={} local_inserts={}",
        RGRS_EXPR_PROBES.load(Relaxed),
        RGRS_EXPR_GLOBAL_HITS.load(Relaxed),
        RGRS_EXPR_GLOBAL_HIT_LOCAL_HITS.load(Relaxed),
        RGRS_EXPR_GLOBAL_HIT_LOCAL_MISSES.load(Relaxed),
        RGRS_EXPR_LOCAL_HITS.load(Relaxed),
        RGRS_EXPR_LOCAL_INSERTS.load(Relaxed),
    );
}

'''
s = stats + s

reuse_old = '''    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        if let Some(r) = self.export_file.dag.exprs.get(&e) {
            return ExprPtr::global(r, r.num_loose_bvars())
        }
        if let Some(r) = self.dag.exprs.get(&e) {
            return ExprPtr::local(r)
        }
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }
'''
reuse_new = '''    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        use std::sync::atomic::Ordering::Relaxed;
        RGRS_EXPR_PROBES.fetch_add(1, Relaxed);
        if let Some(r) = self.export_file.dag.exprs.get(&e) {
            RGRS_EXPR_GLOBAL_HITS.fetch_add(1, Relaxed);
            if self.dag.exprs.get(&e).is_some() {
                RGRS_EXPR_GLOBAL_HIT_LOCAL_HITS.fetch_add(1, Relaxed);
            } else {
                RGRS_EXPR_GLOBAL_HIT_LOCAL_MISSES.fetch_add(1, Relaxed);
            }
            return ExprPtr::global(r, r.num_loose_bvars())
        }
        if let Some(r) = self.dag.exprs.get(&e) {
            RGRS_EXPR_LOCAL_HITS.fetch_add(1, Relaxed);
            return ExprPtr::local(r)
        }
        RGRS_EXPR_LOCAL_INSERTS.fetch_add(1, Relaxed);
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }
'''
probe_old = '''    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        let _ = self.export_file.dag.exprs.get(&e);
        if let Some(r) = self.dag.exprs.get(&e) {
            return ExprPtr::local(r)
        }
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }
'''
probe_new = '''    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        use std::sync::atomic::Ordering::Relaxed;
        RGRS_EXPR_PROBES.fetch_add(1, Relaxed);
        if self.export_file.dag.exprs.get(&e).is_some() {
            RGRS_EXPR_GLOBAL_HITS.fetch_add(1, Relaxed);
        }
        if let Some(r) = self.dag.exprs.get(&e) {
            RGRS_EXPR_LOCAL_HITS.fetch_add(1, Relaxed);
            return ExprPtr::local(r)
        }
        RGRS_EXPR_LOCAL_INSERTS.fetch_add(1, Relaxed);
        ExprPtr::local(self.dag.exprs.insert(self.arena, e))
    }
'''
if reuse_old in s:
    s = s.replace(reuse_old, reuse_new, 1)
elif probe_old in s:
    s = s.replace(probe_old, probe_new, 1)
else:
    raise SystemExit('expected D1 or D2 alloc_expr form not found')
u.write_text(s)

m = Path('src/main.rs')
ms = m.read_text()
old = '    export_file.check_all_declars();\n'
new = '    export_file.check_all_declars();\n    sokonanoda::util::rgrs_dump_expr_stats();\n'
if old not in ms:
    raise SystemExit('main reporting hook not found')
m.write_text(ms.replace(old, new, 1))
print('RGRS global-expression instrumentation applied')
