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

const p=K.Kernel.prototype;
function ensure(k){
 k._termCons??=new Map();k._termObjectIds??=new WeakMap();k._nextTermObjectId??=1;
}
function objectId(k,x){
 ensure(k);let id=k._termObjectIds.get(x);
 if(id!==undefined)return id;
 id=k._nextTermObjectId++;k._termObjectIds.set(x,id);return id;
}
p.make=function(...xs){
 ensure(this);
 const key=JSON.stringify(xs.map(x=>Array.isArray(x)?["array",objectId(this,x)]:[typeof x,x]));
 const old=this._termCons.get(key);
 if(old!==undefined){
   this.__freeConsHits=(this.__freeConsHits??0)+1;
   return old;
 }
 this.tick();
 this.allocations++;
 this._termCons.set(key,xs);
 objectId(this,xs);
 this.__freeConsStores=(this.__freeConsStores??0)+1;
 return xs;
};

const rows=[];
for(const [name,want] of TARGETS){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;
 try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}
 finally{p.run=old;}
 const sum=k=>seen.reduce((n,x)=>n+(x[k]??0),0);
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
   prefixHits:sum("__recPrefixHits"),prefixStores:sum("__recPrefixStores"),
   freeConsHits:sum("__freeConsHits"),freeConsStores:sum("__freeConsStores")};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT",protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"prefix-free-exact-hashcons-hits",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
 claim_boundary:"Execution-accounting consequence only. Structural hash-cons keys and returned terms are identical to the retained structural-sharing layer. An exact cache hit returns the already-constructed immutable term without repaying a construction tick; only a genuinely new node consumes one construction tick and allocation. No typing, conversion, or reduction rule changes."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/prefix-free-exact-hashcons-hits.json",JSON.stringify(out,null,2)+"\n");
console.log("PREFIX_FREE_EXACT_HASHCONS_HITS "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
