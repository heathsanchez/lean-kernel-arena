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

const p=K.Kernel.prototype,prefixRun=p.run,retainedSubstitute=p.substitute,retainedLowerBound=p.lowerBound;
function ensure(k){
 k.__occursFree??=new WeakMap();k.__absentLower??=new WeakMap();k.__exactSubst2??=new WeakMap();
}
function memoDepth(weak,root){
 let m=weak.get(root);if(!m){m=new Map();weak.set(root,m);}return m;
}
function occurs(k,e,d){
 if(!Array.isArray(e))return false;
 ensure(k);const m=memoDepth(k.__occursFree,e);
 if(m.has(d)){k.tick();k.__occursHits=(k.__occursHits??0)+1;return m.get(d);}
 k.tick();k.__occursStores=(k.__occursStores??0)+1;
 let out=false;
 switch(e[0]){
  case "sort":case "const":case "nat":case "strlit":out=false;break;
  case "var":out=e[1]===d;break;
  case "pi":case "lam":out=occurs(k,e[1],d)||occurs(k,e[2],d+1);break;
  case "app":out=occurs(k,e[1],d)||occurs(k,e[2],d);break;
  case "proj":out=occurs(k,e[3],d);break;
  case "let":out=occurs(k,e[1],d)||occurs(k,e[2],d)||occurs(k,e[3],d+1);break;
  default:return true;
 }
 m.set(d,out);return out;
}
function exactMap(k,root,arg){
 let byArg=k.__exactSubst2.get(root);if(!byArg){byArg=new WeakMap();k.__exactSubst2.set(root,byArg);}
 let byDepth=byArg.get(arg);if(!byDepth){byDepth=new Map();byArg.set(arg,byDepth);}return byDepth;
}
p.run=function(...args){
 this.__occursFree=new WeakMap();this.__absentLower=new WeakMap();this.__exactSubst2=new WeakMap();
 return prefixRun.apply(this,args);
};
p.substitute=function(root,arg,depth=0){
 if(!Array.isArray(root)||!Array.isArray(arg))return retainedSubstitute.call(this,root,arg,depth);
 ensure(this);this.__subst2Queries=(this.__subst2Queries??0)+1;
 const abs=memoDepth(this.__absentLower,root);
 if(abs.has(depth)){this.__absentHits=(this.__absentHits??0)+1;return abs.get(depth);}
 if(!occurs(this,root,depth)){
   const out=retainedLowerBound.call(this,root,depth);
   if(out===null)throw new Error("occurrence/lowerBound disagreement");
   abs.set(depth,out);this.__absentStores=(this.__absentStores??0)+1;return out;
 }
 this.__dependentFast=(this.__dependentFast??0)+1;
 const ex=exactMap(this,root,arg);
 if(ex.has(depth)){this.__exact2Hits=(this.__exact2Hits??0)+1;return ex.get(depth);}
 const out=retainedSubstitute.call(this,root,arg,depth);
 ex.set(depth,out);this.__exact2Stores=(this.__exact2Stores??0)+1;return out;
};

const rows=[];
for(const [name,want] of TARGETS){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}finally{p.run=old;}
 const sum=q=>seen.reduce((n,k)=>n+(k[q]??0),0);
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
   prefixHits:sum("__recPrefixHits"),prefixStores:sum("__recPrefixStores"),substQueries:sum("__subst2Queries"),
   occursHits:sum("__occursHits"),occursStores:sum("__occursStores"),absentHits:sum("__absentHits"),
   absentStores:sum("__absentStores"),dependentFast:sum("__dependentFast"),exactHits:sum("__exact2Hits"),exactStores:sum("__exact2Stores")};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT",protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"prefix-shortcircuit-substitution-reuse",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
 claim_boundary:"Execution-only exact reuse. A memoized structural occurrence predicate short-circuits as soon as the target de-Bruijn binder is found. Only proven-absent binders invoke retained lowerBound once and cache its exact result. Binder-dependent substitutions are cached only after retained substitution completes, keyed by exact immutable root identity, argument identity, and depth. No typing, conversion, or reduction law changes."};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/prefix-shortcircuit-substitution-reuse.json",JSON.stringify(out,null,2)+"\n");
console.log("PREFIX_SHORTCIRCUIT_SUBSTITUTION_REUSE "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
