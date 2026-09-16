import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const CASES=[
 ["perf/shared-subterm","ACCEPT",true],["perf/church-numerals","ACCEPT",false],
 ["perf/args-before-unfold","ACCEPT",false],["perf/folded-constant-first","ACCEPT",false],
 ["perf/repeated-subproblem","ACCEPT",false],["perf/discarded-argument-match","ACCEPT",false],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT",false],["undecidability/alg-conv-trans-acc-right","ACCEPT",false],
 ["undecidability/subject-reduction-redex","ACCEPT",false],["undecidability/alg-conv-trans-acc","REJECT",false],
 ["undecidability/subject-reduction-reduct","REJECT",false]
];
const p=K.Kernel.prototype;
async function evaluate(candidate){
  if(candidate){
    await import("./hashcons-hit-reuse-layer.mjs");
    await import("./compiled-dynamic-slot-layer.mjs");
    await import("./closed-subtree-substitution-layer.mjs");
  }
  const rows=[];
  for(const [name,want,focus] of CASES){
    const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
    const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
    const t0=Date.now();let r;
    try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=old;}
    const make={hits:0,misses:0},slot={seedVisits:0,makeKnown:0,makeUnknown:0,queries:0,hits:0,dynamicNodes:0,prefixReused:0},
      subst={queries:0,cacheHits:0,closedSkips:0,visited:0,fallbacks:0};
    if(candidate)for(const k of seen){
      for(const q of Object.keys(make))make[q]+=k.__makeReuseStats?.[q]??0;
      for(const q of Object.keys(slot))slot[q]+=k.__slotStats?.[q]??0;
      for(const q of Object.keys(subst))subst[q]+=k.__closedSubstStats?.[q]??0;
    }
    rows.push({name,want,focus,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      elapsed_ms:Date.now()-t0,make,slot,subst,
      headBetaSpines:seen.reduce((n,k)=>n+(k.__headBetaSpines??0),0),
      prefixHits:seen.reduce((n,k)=>n+(k.__recPrefixHits??0),0)});
  }
  return rows;
}
const baseline=await evaluate(false),candidate=await evaluate(true);
const comparisons=CASES.map(([name,want,focus],i)=>{
 const b=baseline[i],c=candidate[i];
 return {name,want,focus,before:{status:b.status,reason:b.reason,steps:b.steps,constructed:b.constructed,elapsed_ms:b.elapsed_ms},
 after:{status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed,elapsed_ms:c.elapsed_ms},
 make:c.make,slot:c.slot,subst:c.subst,headBetaSpines:c.headBetaSpines,prefixHits:c.prefixHits,
 statusChanged:b.status!==c.status,stepDelta:(c.steps??0)-(b.steps??0),constructedDelta:(c.constructed??0)-(b.constructed??0)};
});
for(const q of comparisons)console.log("ROW "+JSON.stringify(q));
const shared=comparisons[0],changed=comparisons.slice(1).filter(q=>q.after.status!==q.before.status),
 wrong=comparisons.slice(1).filter(q=>q.after.status!==q.want);
const out={experiment:"closed-subtree-substitution",budget:1_000_000,
 sharedClosed:shared.after.status==="ACCEPT",protectedChanged:changed.length,protectedWrong:wrong.length,
 lawful:changed.length===0&&wrong.length===0,
 promotable:shared.after.status==="ACCEPT"&&changed.length===0&&wrong.length===0,comparisons,
 claim_boundary:"Execution-only exact de-Bruijn pruning. Compositional support metadata is seeded only after retained validation and propagated through immutable terms. Any subtree with certified support 0 contains no free variables relative to its own binders, so substitution returns that exact immutable subtree by identity without traversal. Nonclosed standard syntax follows the retained de-Bruijn rules and exact per-(term,arg,depth) memoization; unknown syntax falls back to the frozen retained substitute. Composed with exact hash-cons hit reuse. No typing, equality, reduction, or rejection rule changes."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/closed-subtree-substitution.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("CLOSED_SUBTREE_SUBSTITUTION "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
