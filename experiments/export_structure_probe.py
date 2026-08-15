#!/usr/bin/env python3
"""Streaming structural probe for Lean 4 export NDJSON.

Computes representation-only statistics before any kernel/checker is run.
The key metric is binder absence: for lam/forallE/letE bodies, whether de Bruijn
index 0 is absent from the body's free-variable mask. This mirrors the structural
condition used by sokonanoda's ignores_binder/absent-argument optimization.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

MASK64 = (1 << 64) - 1


def shift_binder(mask: int) -> int:
    return mask >> 1


def get_mask(masks: dict[int, int], i: int) -> int:
    return masks.get(i, 0)


def analyze(path: Path) -> dict:
    masks: dict[int, int] = {}
    kinds = Counter()
    decls = Counter()
    total_lines = 0
    exprs = 0
    binders = 0
    absent_binders = 0
    dependent_binders = 0
    app_nodes = 0
    let_nondep_declared = 0
    let_absent_computed = 0

    with path.open("r", encoding="utf-8") as f:
        for line in f:
            total_lines += 1
            obj = json.loads(line)
            if "ie" in obj:
                ie = int(obj["ie"])
                exprs += 1
                if "bvar" in obj:
                    k = int(obj["bvar"])
                    m = (1 << k) if k < 64 else 0
                    kinds["bvar"] += 1
                elif "sort" in obj:
                    m = 0; kinds["sort"] += 1
                elif "const" in obj:
                    m = 0; kinds["const"] += 1
                elif "app" in obj:
                    x = obj["app"]
                    m = get_mask(masks, int(x["fn"])) | get_mask(masks, int(x["arg"]))
                    kinds["app"] += 1; app_nodes += 1
                elif "lam" in obj or "forallE" in obj:
                    key = "lam" if "lam" in obj else "forallE"
                    x = obj[key]
                    body_m = get_mask(masks, int(x["body"]))
                    type_m = get_mask(masks, int(x["type"]))
                    binders += 1
                    if body_m & 1:
                        dependent_binders += 1
                    else:
                        absent_binders += 1
                    m = type_m | shift_binder(body_m)
                    kinds[key] += 1
                elif "letE" in obj:
                    x = obj["letE"]
                    body_m = get_mask(masks, int(x["body"]))
                    type_m = get_mask(masks, int(x["type"]))
                    value_m = get_mask(masks, int(x["value"]))
                    binders += 1
                    absent = (body_m & 1) == 0
                    if absent:
                        absent_binders += 1; let_absent_computed += 1
                    else:
                        dependent_binders += 1
                    if bool(x.get("nondep", False)):
                        let_nondep_declared += 1
                    m = type_m | value_m | shift_binder(body_m)
                    kinds["letE"] += 1
                elif "proj" in obj:
                    m = get_mask(masks, int(obj["proj"]["struct"])); kinds["proj"] += 1
                elif "mdata" in obj:
                    m = get_mask(masks, int(obj["mdata"]["expr"])); kinds["mdata"] += 1
                elif "natVal" in obj:
                    m = 0; kinds["natVal"] += 1
                elif "strVal" in obj:
                    m = 0; kinds["strVal"] += 1
                else:
                    m = 0; kinds["other_expr"] += 1
                masks[ie] = m & MASK64
            else:
                for k in ("axiom", "def", "opaque", "thm", "quot", "inductive"):
                    if k in obj:
                        decls[k] += 1
                        break

    absent_rate = absent_binders / binders if binders else 0.0
    dependent_rate = dependent_binders / binders if binders else 0.0
    return {
        "file": str(path),
        "bytes": path.stat().st_size,
        "lines": total_lines,
        "exprs": exprs,
        "apps": app_nodes,
        "binders": binders,
        "absent_binders": absent_binders,
        "dependent_binders": dependent_binders,
        "absent_binder_rate": absent_rate,
        "dependent_binder_rate": dependent_rate,
        "apps_per_expr": app_nodes / exprs if exprs else 0.0,
        "binders_per_expr": binders / exprs if exprs else 0.0,
        "let_nondep_declared": let_nondep_declared,
        "let_absent_computed": let_absent_computed,
        "expr_kinds": dict(kinds),
        "declarations": dict(decls),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+", type=Path)
    ap.add_argument("--jsonl", action="store_true")
    args = ap.parse_args()
    rows = [analyze(p) for p in args.paths]
    if args.jsonl:
        for r in rows:
            print(json.dumps(r, sort_keys=True))
    else:
        print(json.dumps(rows, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
