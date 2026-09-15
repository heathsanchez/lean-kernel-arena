import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./recursor-prefix-cache-layer.mjs");

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
const p=K.Kernel.prototype,run0=p.run,shift0=p.shift;
p.run=function(...args){this.__prefixZeroShiftHits=0;return run0.apply(this,args);};
p.shift=function(e,amount,cut=0){
  if(amount===0){this.__prefixZeroShiftHits=(this.__prefixZeroShiftHits??0)+1;return e;}
  return shift0.call(this,e,amount,cut);
};
const rows=[];
for(const [name,want] of TARGETS){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;
 try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}
 finally{p.run=old;}
 const sum=q=>seen.reduce((n,k)=>n+(k[q]??0),0);
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
   prefixHits:sum("__recPrefixHits"),prefixStores:sum("__recPrefixStores"),zeroShiftHits:sum("__prefixZeroShiftHits")};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT",protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"prefix-zero-shift-composition",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
 claim_boundary:"Composition of two exact execution consequences only: exact recursor-prefix specialization plus the identity shift(t,0)=t. No typing, conversion, declaration, substitution, or reduction law is changed."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/prefix-zero-shift-composition.json",JSON.stringify(out,null,2)+"\n");
console.log("PREFIX_ZERO_SHIFT_COMPOSITION "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
