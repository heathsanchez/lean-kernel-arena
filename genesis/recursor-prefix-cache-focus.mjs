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
const p=K.Kernel.prototype,rows=[];
for(const [name,want] of TARGETS){
  const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  const t0=Date.now();let r;
  try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}
  finally{p.run=old;}
  const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
    prefixHits:seen.reduce((n,k)=>n+(k.__recPrefixHits??0),0),
    prefixStores:seen.reduce((n,k)=>n+(k.__recPrefixStores??0),0),
    prefixReductions:seen.reduce((n,k)=>n+(k.__recPrefixReductions??0),0)};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const protectedClean=rows.slice(1).every(r=>r.status===r.want);
const sharedClosed=rows[0]?.status==="ACCEPT";
const out={experiment:"recursor-prefix-cache-focus",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/recursor-prefix-cache-focus.json",JSON.stringify(out,null,2)+"\n");
console.log("RECURSOR_PREFIX_CACHE_FOCUS "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
