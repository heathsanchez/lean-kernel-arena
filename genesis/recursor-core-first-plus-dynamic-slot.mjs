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
async function evaluate(candidate,budget=1_000_000){
  if(candidate){
    await import("./compiled-dynamic-slot-layer.mjs");
    await import("./recursor-core-first-layer.mjs");
  }
  const rows=[];
  for(const [name,want,focus] of CASES){
    const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
    const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
    const t0=Date.now();let r;
    try{r=K.checkExport(input,CAPS,budget);}finally{p.run=old;}
    const slot={seedVisits:0,makeKnown:0,makeUnknown:0,queries:0,hits:0,dynamicNodes:0,prefixReused:0};
    const core={splits:0,hits:0,stores:0,reentries:0};
    if(candidate)for(const k of seen){
      for(const q of Object.keys(slot))slot[q]+=k.__slotStats?.[q]??0;
      for(const q of Object.keys(core))core[q]+=k.__recCoreStats?.[q]??0;
    }
    rows.push({name,want,focus,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
      elapsed_ms:Date.now()-t0,slot,core});
  }
  return rows;
}
const baseline=await evaluate(false),candidate=await evaluate(true);
const comparisons=CASES.map(([name,want,focus],i)=>{
 const b=baseline[i],c=candidate[i];
 return {name,want,focus,before:b,after:c,statusChanged:b.status!==c.status,
   stepDelta:(c.steps??0)-(b.steps??0),constructedDelta:(c.constructed??0)-(b.constructed??0)};
});
for(const q of comparisons)console.log("ROW "+JSON.stringify(q));
const shared=comparisons[0],changed=comparisons.slice(1).filter(q=>q.after.status!==q.before.status),
 wrong=comparisons.slice(1).filter(q=>q.after.status!==q.want);
let cliff=null;if(shared.after.status!=="ACCEPT"){cliff=(await evaluate(true,2_000_000))[0];console.log("CLIFF "+JSON.stringify(cliff));}
const out={experiment:"recursor-core-first-plus-dynamic-slot",budget:1_000_000,
 sharedClosed:shared.after.status==="ACCEPT",protectedChanged:changed.length,protectedWrong:wrong.length,
 lawful:changed.length===0&&wrong.length===0,
 promotable:shared.after.status==="ACCEPT"&&changed.length===0&&wrong.length===0,
 comparisons,cliff,
 claim_boundary:"Exact evaluation-order refinement. For ordinary-kernel recursor applications with arguments beyond semantic recursor arity, the saturated core through the major premise is weak-head-reduced before extra arguments are attached. The four-argument closed-prefix substitution consequence is composed independently. LocalDef execution is excluded. No typing, equality, iota, beta, or recursor rule is added or omitted."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/recursor-core-first-plus-dynamic-slot.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("RECURSOR_CORE_FIRST_PLUS_DYNAMIC_SLOT "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
