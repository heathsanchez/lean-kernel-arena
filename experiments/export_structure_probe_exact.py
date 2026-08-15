#!/usr/bin/env python3
"""Exact structural probe for Lean export NDJSON.

Unlike the earlier exploratory probe, this version does NOT truncate de Bruijn
free-variable masks to 64 bits. Python integers are used as unbounded bitsets,
so a bvar index >=64 remains observable. Intended first for focused fixtures and
mechanism validation before any large-corpus use.
"""
from __future__ import annotations
import argparse, json
from collections import Counter
from pathlib import Path

def get_mask(masks: dict[int,int], i:int)->int:
    return masks.get(i,0)

def analyze(path: Path)->dict:
    masks: dict[int,int] = {}
    kinds=Counter(); binders=absent=dependent=apps=exprs=0
    max_bvar=-1
    with path.open('r',encoding='utf-8') as f:
        for line in f:
            obj=json.loads(line)
            if 'ie' not in obj: continue
            ie=int(obj['ie']); exprs += 1
            if 'bvar' in obj:
                k=int(obj['bvar']); max_bvar=max(max_bvar,k); m=1<<k; kinds['bvar']+=1
            elif 'sort' in obj: m=0; kinds['sort']+=1
            elif 'const' in obj: m=0; kinds['const']+=1
            elif 'app' in obj:
                x=obj['app']; m=get_mask(masks,int(x['fn']))|get_mask(masks,int(x['arg'])); apps+=1; kinds['app']+=1
            elif 'lam' in obj or 'forallE' in obj:
                key='lam' if 'lam' in obj else 'forallE'; x=obj[key]
                body=get_mask(masks,int(x['body'])); typ=get_mask(masks,int(x['type']))
                binders+=1
                if body & 1: dependent+=1
                else: absent+=1
                m=typ | (body>>1); kinds[key]+=1
            elif 'letE' in obj:
                x=obj['letE']; body=get_mask(masks,int(x['body'])); typ=get_mask(masks,int(x['type'])); val=get_mask(masks,int(x['value']))
                binders+=1
                if body & 1: dependent+=1
                else: absent+=1
                m=typ|val|(body>>1); kinds['letE']+=1
            elif 'proj' in obj: m=get_mask(masks,int(obj['proj']['struct'])); kinds['proj']+=1
            elif 'mdata' in obj: m=get_mask(masks,int(obj['mdata']['expr'])); kinds['mdata']+=1
            else: m=0; kinds['other']+=1
            masks[ie]=m
    return {
      'file':str(path),'exprs':exprs,'apps':apps,'binders':binders,
      'absent_binders':absent,'dependent_binders':dependent,
      'absent_binder_rate': absent/binders if binders else 0.0,
      'dependent_binder_rate': dependent/binders if binders else 0.0,
      'max_bvar_index': max_bvar,'expr_kinds':dict(kinds)
    }

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('paths',nargs='+',type=Path); args=ap.parse_args()
    for p in args.paths: print(json.dumps(analyze(p),sort_keys=True))
if __name__=='__main__': main()
