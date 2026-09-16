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
  if(candidate)await import("./private-whnf-environment-layer.mjs");
  const rows=[];
  for(const [name,want,focus] of TARGETS){
    const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
    const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
    const t0=Date.now();let r;
    try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=old;}
    const st={queries:0,targetCalls:0,closureSteps:0,beta:0,defs:0,recs:0,vars:0,lets:0,
      materialized:0,reusedClosed:0,reusedNoEnv:0,paramChecks:0,maxEnv:0,maxArgs:0};
    if(candidate)for(const k of seen)for(const q of Object.keys(st)){
      if(q==="maxEnv"||q==="maxArgs")st[q]=Math.max(st[q],k.__privateStats?.[q]??0);
      else st[q]+=k.__privateStats?.[q]??0;
    }
    const sum=q=>seen.reduce((n,k)=>n+(k[q]??0),0);
    rows.push({name,want,focus,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,elapsed_ms:Date.now()-t0,privateEnv:st,
      headBetaSpines:sum("__headBetaSpines"),prefixHits:sum("__recPrefixHits")});
  }
  return rows;
}
const baseline=await evaluate(false),candidate=await evaluate(true);
const comparisons=TARGETS.map(([name,want,focus],i)=>{
 const b=baseline[i],c=candidate[i];
 return {name,want,focus,before:{status:b.status,reason:b.reason,steps:b.steps,constructed:b.constructed,elapsed_ms:b.elapsed_ms},
   after:{status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed,elapsed_ms:c.elapsed_ms},
   privateEnv:c.privateEnv,headBetaSpines:c.headBetaSpines,prefixHits:c.prefixHits,
   statusChanged:b.status!==c.status,constructedDelta:(c.constructed??0)-(b.constructed??0)};
});
for(const q of comparisons)console.log("ROW "+JSON.stringify(q));
const shared=comparisons[0],changed=comparisons.slice(1).filter(q=>q.after.status!==q.before.status),
 wrong=comparisons.slice(1).filter(q=>q.after.status!==q.want);
const out={experiment:"private-whnf-environment-separator",budget:1_000_000,
 sharedClosed:shared.after.status==="ACCEPT",targetCalls:shared.privateEnv.targetCalls,
 protectedChanged:changed.length,protectedWrong:wrong.length,
 lawful:changed.length===0&&wrong.length===0,
 promotable:shared.after.status==="ACCEPT"&&changed.length===0&&wrong.length===0,
 comparisons,
 claim_boundary:"The closure environment is private to WHNF and never enters the ordinary AST or identity-keyed caches. Only depth-zero substitutions occurring under WHNF with a five-argument constant-headed body enter the closure machine. Definitions and ordinary recursor rules may consume the environment directly; before control returns to retained code the result is materialized as ordinary term arrays. All other substitutions and all unsupported closure states use the frozen retained implementation."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/private-whnf-environment-separator.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("PRIVATE_WHNF_ENVIRONMENT_SEPARATOR "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
