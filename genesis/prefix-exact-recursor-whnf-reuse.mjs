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

const p=K.Kernel.prototype,prefixRun=p.run,prefixWhnf=p.whnf;
function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {h,args};}
function eligible(k,e){
 if(k.localDefs||!Array.isArray(e)||e[0]!=="app")return false;
 const {h,args}=spine(e);if(!Array.isArray(h)||h[0]!=="const")return false;
 const d=k.env?.get(h[1]);if(d?.kind!=="rec")return false;
 return args.length>=d.numParams+1+d.numMinors+d.numIndices+1;
}
p.run=function(...args){
 this.__recWhnf=new WeakMap();this.__recWhnfBusy=new WeakSet();
 return prefixRun.apply(this,args);
};
p.whnf=function(e){
 if(!eligible(this,e))return prefixWhnf.call(this,e);
 this.__recWhnf??=new WeakMap();this.__recWhnfBusy??=new WeakSet();
 if(this.__recWhnf.has(e)){this.__recWhnfHits=(this.__recWhnfHits??0)+1;return this.__recWhnf.get(e);}
 if(this.__recWhnfBusy.has(e))return prefixWhnf.call(this,e);
 this.__recWhnfBusy.add(e);
 try{
   const out=prefixWhnf.call(this,e);
   this.__recWhnf.set(e,out);this.__recWhnfStores=(this.__recWhnfStores??0)+1;
   return out;
 }finally{this.__recWhnfBusy.delete(e);}
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
   recWhnfHits:sum("__recWhnfHits"),recWhnfStores:sum("__recWhnfStores")};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT",protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"prefix-exact-recursor-whnf-reuse",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
 claim_boundary:"Execution-only reuse. Successful weak-head reduction of a fully supplied recursor application is cached only by exact immutable expression identity for the current monotonic kernel run. Local-definition contexts and failed/in-progress reductions are excluded. Recursor-prefix specialization remains exact."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/prefix-exact-recursor-whnf-reuse.json",JSON.stringify(out,null,2)+"\n");
console.log("PREFIX_EXACT_RECURSOR_WHNF_REUSE "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
