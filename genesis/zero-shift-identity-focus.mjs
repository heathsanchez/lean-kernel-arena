import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT"],["perf/church-numerals","ACCEPT"],
 ["perf/args-before-unfold","ACCEPT"],["perf/folded-constant-first","ACCEPT"],
 ["perf/repeated-subproblem","ACCEPT"],["perf/discarded-argument-match","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT"],
 ["undecidability/subject-reduction-redex","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"],
 ["undecidability/subject-reduction-reduct","REJECT"]
];

const p=K.Kernel.prototype,retainedRun=p.run,retainedShift=p.shift;
p.run=function(...args){
  this.__zeroShiftHits=0;
  return retainedRun.apply(this,args);
};
p.shift=function(e,amount,cut=0){
  if(amount===0){
    this.__zeroShiftHits=(this.__zeroShiftHits??0)+1;
    return e;
  }
  return retainedShift.call(this,e,amount,cut);
};

const rows=[];
for(const [name,want] of TARGETS){
  const seen=[],old=p.run;
  p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  const t0=Date.now();let r;
  try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}
  finally{p.run=old;}
  const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    elapsed_ms:Date.now()-t0,zeroShiftHits:seen.reduce((n,k)=>n+(k.__zeroShiftHits??0),0)};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT";
const protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"zero-shift-identity-focus",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
 claim_boundary:"Execution identity only: de-Bruijn shifting by amount zero is exactly the identity on every retained term constructor, so the candidate returns the immutable input term directly instead of recursively rebuilding it. No typing, conversion, substitution, reduction, or declaration rule changes."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/zero-shift-identity-focus.json",JSON.stringify(out,null,2)+"\n");
console.log("ZERO_SHIFT_IDENTITY_FOCUS "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
