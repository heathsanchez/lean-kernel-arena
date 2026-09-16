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
  if(candidate)await import("./dynamic-slot-closure-layer.mjs");
  const rows=[];
  for(const [name,want,focus] of TARGETS){
    const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
    const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
    const t0=Date.now();let r;
    try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=old;}
    const dyn={queries:0,targetCalls:0,lazySlots:0,closures:0,closureHits:0,forcedNodes:0,
      maskHits:0,maskStores:0,reusedClosed:0};
    if(candidate)for(const k of seen)for(const q of Object.keys(dyn))dyn[q]+=k.__dynamicStats?.[q]??0;
    const sum=q=>seen.reduce((n,k)=>n+(k[q]??0),0);
    rows.push({name,want,focus,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,elapsed_ms:Date.now()-t0,dynamic:dyn,
      headBetaSpines:sum("__headBetaSpines"),prefixHits:sum("__recPrefixHits")});
  }
  return rows;
}
const baseline=await evaluate(false),candidate=await evaluate(true);
const comparisons=TARGETS.map(([name,want,focus],i)=>{
 const b=baseline[i],c=candidate[i];
 return {name,want,focus,before:{status:b.status,reason:b.reason,steps:b.steps,constructed:b.constructed,elapsed_ms:b.elapsed_ms},
   after:{status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed,elapsed_ms:c.elapsed_ms},
   dynamic:c.dynamic,headBetaSpines:c.headBetaSpines,prefixHits:c.prefixHits,
   statusChanged:b.status!==c.status,constructedDelta:(c.constructed??0)-(b.constructed??0)};
});
for(const q of comparisons)console.log("ROW "+JSON.stringify(q));
const shared=comparisons[0],protectedChanged=comparisons.slice(1).filter(q=>q.after.status!==q.before.status),
 protectedWrong=comparisons.slice(1).filter(q=>q.after.status!==q.want);
const out={experiment:"dynamic-slot-closure-separator",budget:1_000_000,
 sharedClosed:shared.after.status==="ACCEPT",targetCalls:shared.dynamic.targetCalls,
 protectedChanged:protectedChanged.length,protectedWrong:protectedWrong.length,
 lawful:protectedChanged.length===0&&protectedWrong.length===0,
 promotable:shared.after.status==="ACCEPT"&&protectedChanged.length===0&&protectedWrong.length===0,
 comparisons,
 claim_boundary:"Exact residual-specific execution repair selected by structural dependency, not problem identity. Only depth-zero substitutions whose root is a five-argument application with closed head, four closed arguments, and exactly one argument depending on binder 0 retain that dynamic argument as a lazy de-Bruijn closure. All other substitution is the frozen retained implementation. The candidate is composed prospectively with the previously measured head-beta and recursor-prefix execution consequences."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/dynamic-slot-closure-separator.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("DYNAMIC_SLOT_CLOSURE_SEPARATOR "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
