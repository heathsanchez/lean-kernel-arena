import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./recursive-def-shallow-conversion-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT"],
 ["perf/church-numerals","ACCEPT"],
 ["perf/args-before-unfold","ACCEPT"],
 ["perf/folded-constant-first","ACCEPT"],
 ["perf/repeated-subproblem","ACCEPT"],
 ["perf/discarded-argument-match","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-right","ACCEPT"],
 ["undecidability/subject-reduction-redex","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"],
 ["undecidability/subject-reduction-reduct","REJECT"]
];

const p=K.Kernel.prototype,rows=[];
for(const [name,want] of TARGETS){
  const seen=[],old=p.run;
  p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  const t0=Date.now();let r;
  try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}
  finally{p.run=old;}
  const sum=q=>seen.reduce((n,k)=>n+(k[q]??0),0);
  const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
    shallowTransactions:sum("__shallowTransactions"),shallowSuccesses:sum("__shallowSuccesses"),
    shallowDeltas:sum("__shallowDeltas"),shallowIotas:sum("__shallowIotas"),
    shallowMajorSteps:sum("__shallowMajorSteps"),zeroShifts:sum("__shallowZeroShifts")};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT";
const protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"recursive-def-shallow-focus",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
 claim_boundary:"Transactional shallow conversion only when two distinct checked definitions are independently detected as recursor-sensitive. They are unfolded and iota-reduced in lock-step and compared at common heads before retained deep normalization. Failed shallow paths restore steps, budget, and conversion frontier exactly. No new definitional equality law."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/recursive-def-shallow-focus.json",JSON.stringify(out,null,2)+"\n");
console.log("RECURSIVE_DEF_SHALLOW_FOCUS "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
