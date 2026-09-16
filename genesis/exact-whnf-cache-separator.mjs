import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const CASES=[
 ["perf/shared-subterm","ACCEPT",true],
 ["perf/church-numerals","ACCEPT",false],
 ["perf/args-before-unfold","ACCEPT",false],
 ["perf/folded-constant-first","ACCEPT",false],
 ["perf/repeated-subproblem","ACCEPT",false],
 ["perf/discarded-argument-match","ACCEPT",false],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT",false],
 ["undecidability/alg-conv-trans-acc-right","ACCEPT",false],
 ["undecidability/subject-reduction-redex","ACCEPT",false],
 ["undecidability/alg-conv-trans-acc","REJECT",false],
 ["undecidability/subject-reduction-reduct","REJECT",false]
];
const p=K.Kernel.prototype;

async function evaluate(candidate,budget=1_000_000){
  if(candidate)await import("./exact-whnf-cache-layer.mjs");
  const rows=[];
  for(const [name,want,focus] of CASES){
    const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
    const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
    const t0=Date.now();let r;
    try{r=K.checkExport(input,CAPS,budget);}finally{p.run=old;}
    rows.push({name,want,focus,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
      elapsed_ms:Date.now()-t0,
      whnfHits:seen.reduce((n,k)=>n+(k.__whnfExactHits??0),0),
      whnfStores:seen.reduce((n,k)=>n+(k.__whnfExactStores??0),0)});
  }
  return rows;
}
const baseline=await evaluate(false,1_000_000);
const candidate=await evaluate(true,1_000_000);
const comparisons=CASES.map(([name,want,focus],i)=>{
 const b=baseline[i],c=candidate[i];
 return {name,want,focus,before:b,after:c,statusChanged:b.status!==c.status,
   stepDelta:(c.steps??0)-(b.steps??0),constructedDelta:(c.constructed??0)-(b.constructed??0)};
});
for(const q of comparisons)console.log("ROW "+JSON.stringify(q));
const shared=comparisons[0],changed=comparisons.slice(1).filter(q=>q.after.status!==q.before.status),
 wrong=comparisons.slice(1).filter(q=>q.after.status!==q.want);
let cliff=null;
if(shared.after.status!=="ACCEPT"){
  const rows=await evaluate(true,2_000_000);
  cliff=rows[0];
  console.log("CLIFF "+JSON.stringify(cliff));
}
const out={experiment:"exact-whnf-cache-separator",budget:1_000_000,
 sharedClosed:shared.after.status==="ACCEPT",protectedChanged:changed.length,protectedWrong:wrong.length,
 lawful:changed.length===0&&wrong.length===0,
 promotable:shared.after.status==="ACCEPT"&&changed.length===0&&wrong.length===0,
 comparisons,cliff,
 claim_boundary:"Execution consequence reuse only. Successful retained WHNF of an exact immutable ordinary term node is cached by object identity for the current run. Local-definition execution is excluded. No failure, UNKNOWN, REJECT, equality judgment, typing result, or structurally similar term is cached."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/exact-whnf-cache-separator.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("EXACT_WHNF_CACHE_SEPARATOR "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
