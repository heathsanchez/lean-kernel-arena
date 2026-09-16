import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT",true],["perf/church-numerals","ACCEPT",false],
 ["perf/args-before-unfold","ACCEPT",false],["perf/folded-constant-first","ACCEPT",false],
 ["perf/repeated-subproblem","ACCEPT",false],["perf/discarded-argument-match","ACCEPT",false],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT",false],["undecidability/alg-conv-trans-acc-right","ACCEPT",false],
 ["undecidability/subject-reduction-redex","ACCEPT",false],["undecidability/alg-conv-trans-acc","REJECT",false],
 ["undecidability/subject-reduction-reduct","REJECT",false]
];
const p=K.Kernel.prototype;

async function evaluate(candidate){
  if(candidate)await import("./dynamic-fifth-substitution-layer.mjs");
  const rows=[];
  for(const [name,want,focus] of TARGETS){
    const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
    const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
    const t0=Date.now();let r;
    try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=old;}
    const stats={queries:0,direct:0,unchanged:0,rebuilt:0,supportHits:0,supportStores:0};
    if(candidate)for(const k of seen)for(const q of Object.keys(stats))stats[q]+=k.__slotStats?.[q]??0;
    rows.push({name,want,focus,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,elapsed_ms:Date.now()-t0,slot:stats});
  }
  return rows;
}
const baseline=await evaluate(false),candidate=await evaluate(true);
const comparisons=TARGETS.map(([name,want,focus],i)=>{
  const b=baseline[i],c=candidate[i];
  return {name,want,focus,
    before:{status:b.status,reason:b.reason,steps:b.steps,constructed:b.constructed,elapsed_ms:b.elapsed_ms},
    after:{status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed,elapsed_ms:c.elapsed_ms},
    slot:c.slot,statusChanged:b.status!==c.status,
    stepDelta:(c.steps??0)-(b.steps??0),constructedDelta:(c.constructed??0)-(b.constructed??0)};
});
for(const q of comparisons)console.log("ROW "+JSON.stringify(q));
const shared=comparisons[0];
const changed=comparisons.slice(1).filter(q=>q.after.status!==q.before.status);
const wrong=comparisons.slice(1).filter(q=>q.after.status!==q.want);
const out={experiment:"dynamic-fifth-substitution-separator",budget:1_000_000,
  sharedClosed:shared.after.status==="ACCEPT",protectedChanged:changed.length,protectedWrong:wrong.length,
  lawful:changed.length===0&&wrong.length===0,
  promotable:shared.after.status==="ACCEPT"&&changed.length===0&&wrong.length===0,
  comparisons,
  claim_boundary:"Exact de-Bruijn substitution consequence for the measured residual: when a five-argument constant-headed application has a closed function prefix (head plus first four arguments), depth-zero substitution reuses that prefix by pointer identity and applies the frozen retained substitution only to the fifth argument. Closedness is computed exactly and cached by immutable term identity; first analysis of each node is budget-accounted. No typing, equality, reduction, or rejection rule is added."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/dynamic-fifth-substitution-separator.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("DYNAMIC_FIFTH_SUBSTITUTION_SEPARATOR "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
