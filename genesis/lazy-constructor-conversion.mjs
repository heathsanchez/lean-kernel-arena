import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const CASES=[["perf/shared-subterm","ACCEPT",true],["perf/church-numerals","ACCEPT",false],["perf/args-before-unfold","ACCEPT",false],["perf/folded-constant-first","ACCEPT",false],["perf/repeated-subproblem","ACCEPT",false],["perf/discarded-argument-match","ACCEPT",false],["undecidability/alg-conv-trans-acc-left","ACCEPT",false],["undecidability/alg-conv-trans-acc-right","ACCEPT",false],["undecidability/subject-reduction-redex","ACCEPT",false],["undecidability/alg-conv-trans-acc","REJECT",false],["undecidability/subject-reduction-reduct","REJECT",false]];
const p=K.Kernel.prototype;
async function evalAll(candidate){
 if(candidate)await import("./lazy-constructor-conversion-layer.mjs");
 const rows=[];
 for(const [name,want,focus] of CASES){
  const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=old;}
  const st={attempts:0,successes:0,aborts:0,pairs:0,ctorPairs:0,whnfHits:0,whnfStores:0,maxWork:0};
  if(candidate)for(const k of seen)for(const q of Object.keys(st))st[q]=q==="maxWork"?Math.max(st[q],k.__lazyCtorStats?.[q]??0):st[q]+(k.__lazyCtorStats?.[q]??0);
  rows.push({name,want,focus,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,stats:st});
 }
 return rows;
}
const baseline=await evalAll(false),candidate=await evalAll(true);
const cmp=CASES.map(([name,want,focus],i)=>({name,want,focus,before:baseline[i],after:candidate[i],statusChanged:baseline[i].status!==candidate[i].status}));
for(const q of cmp)console.log("ROW "+JSON.stringify(q));
const shared=cmp[0],changed=cmp.slice(1).filter(q=>q.statusChanged),wrong=cmp.slice(1).filter(q=>q.after.status!==q.want);
const out={experiment:"lazy-constructor-conversion",sharedClosed:shared.after.status==="ACCEPT",protectedChanged:changed.length,protectedWrong:wrong.length,lawful:changed.length===0&&wrong.length===0,promotable:shared.after.status==="ACCEPT"&&changed.length===0&&wrong.length===0,comparisons:cmp};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});writeFileSync(new URL("./evidence/lazy-constructor-conversion.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("LAZY_CONSTRUCTOR_CONVERSION "+JSON.stringify(out));if(!out.promotable)process.exit(1);
