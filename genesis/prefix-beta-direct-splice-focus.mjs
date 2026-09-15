import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./scoped-beta-direct-splice-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT"],["perf/church-numerals","ACCEPT"],
 ["perf/args-before-unfold","ACCEPT"],["perf/folded-constant-first","ACCEPT"],
 ["perf/repeated-subproblem","ACCEPT"],["perf/discarded-argument-match","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT"],["undecidability/subject-reduction-redex","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"],["undecidability/subject-reduction-reduct","REJECT"]
];
const p=K.Kernel.prototype,rows=[];
for(const [name,want] of TARGETS){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;
 try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}
 finally{p.run=old;}
 const sum=q=>seen.reduce((n,k)=>n+(k[q]??0),0);
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
   betaSpliceHits:sum("__betaSpliceHits"),prefixHits:sum("__recPrefixHits"),prefixStores:sum("__recPrefixStores")};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT",protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"prefix-beta-direct-splice-focus",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
 claim_boundary:"Exact execution sharing only. In a retained multi-beta materialization, when a captured argument requires zero de-Bruijn shift, the immutable argument is spliced directly instead of recursively copied. Nonzero-shift captures follow the retained materializer. Composed with exact recursor-prefix reuse; no typing, conversion, declaration, or reduction rule changes."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/prefix-beta-direct-splice-focus.json",JSON.stringify(out,null,2)+"\n");
console.log("PREFIX_BETA_DIRECT_SPLICE_FOCUS "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
