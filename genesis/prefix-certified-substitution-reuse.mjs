import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT"],
 ["perf/church-numerals","ACCEPT"],["perf/args-before-unfold","ACCEPT"],
 ["perf/folded-constant-first","ACCEPT"],["perf/repeated-subproblem","ACCEPT"],
 ["perf/discarded-argument-match","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT"],
 ["undecidability/subject-reduction-redex","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"],
 ["undecidability/subject-reduction-reduct","REJECT"]
];

const p=K.Kernel.prototype;
const prefixRun=p.run, retainedSubstitute=p.substitute, retainedLowerBound=p.lowerBound;
const fallbackable=e=>e instanceof K.Stop||e instanceof RangeError;

function ensure(k){
  k.__binderIndependence??=new WeakMap();
  k.__exactSubst??=new WeakMap();
}
function independentSlot(k,root){
  ensure(k);
  let m=k.__binderIndependence.get(root);
  if(!m){m=new Map();k.__binderIndependence.set(root,m);}
  return m;
}
function exactSlot(k,root,arg){
  ensure(k);
  let byArg=k.__exactSubst.get(root);
  if(!byArg){byArg=new WeakMap();k.__exactSubst.set(root,byArg);}
  let byDepth=byArg.get(arg);
  if(!byDepth){byDepth=new Map();byArg.set(arg,byDepth);}
  return byDepth;
}

p.run=function(...args){
  this.__binderIndependence=new WeakMap();
  this.__exactSubst=new WeakMap();
  return prefixRun.apply(this,args);
};

p.substitute=function(root,arg,depth=0){
  if(!Array.isArray(root)||!Array.isArray(arg))
    return retainedSubstitute.call(this,root,arg,depth);
  ensure(this);
  this.__substQueries=(this.__substQueries??0)+1;

  const indep=independentSlot(this,root);
  if(indep.has(depth)){
    const entry=indep.get(depth);
    if(entry.absent){
      this.__independentHits=(this.__independentHits??0)+1;
      return entry.out;
    }
  } else {
    try{
      const out=retainedLowerBound.call(this,root,depth);
      if(out!==null){
        indep.set(depth,{absent:true,out});
        this.__independentStores=(this.__independentStores??0)+1;
        return out;
      }
      indep.set(depth,{absent:false});
      this.__dependentStores=(this.__dependentStores??0)+1;
    }catch(e){
      if(!fallbackable(e))throw e;
      this.__independenceFailures=(this.__independenceFailures??0)+1;
    }
  }

  const exact=exactSlot(this,root,arg);
  if(exact.has(depth)){
    this.__exactHits=(this.__exactHits??0)+1;
    return exact.get(depth);
  }
  const out=retainedSubstitute.call(this,root,arg,depth);
  exact.set(depth,out);
  this.__exactStores=(this.__exactStores??0)+1;
  return out;
};

const rows=[];
for(const [name,want] of TARGETS){
  const seen=[],old=p.run;
  p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  const t0=Date.now();let r;
  try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}
  finally{p.run=old;}
  const sum=key=>seen.reduce((n,k)=>n+(k[key]??0),0);
  const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
    prefixHits:sum("__recPrefixHits"),prefixStores:sum("__recPrefixStores"),
    substQueries:sum("__substQueries"),independentHits:sum("__independentHits"),
    independentStores:sum("__independentStores"),dependentStores:sum("__dependentStores"),
    exactHits:sum("__exactHits"),exactStores:sum("__exactStores"),
    independenceFailures:sum("__independenceFailures")};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const sharedClosed=rows[0]?.status==="ACCEPT";
const protectedClean=rows.slice(1).every(r=>r.status===r.want);
const out={experiment:"prefix-certified-substitution-reuse",sharedClosed,protectedClean,promotable:sharedClosed&&protectedClean,rows,
  claim_boundary:"Execution-only consequence composition. Recursor-prefix specialization is exact. A successful lowerBound(root,depth) proves the eliminated binder absent and its lowered result argument-independent; dependent substitutions are memoized only by exact immutable root identity, exact argument identity and exact depth after retained substitution completes. No conversion, typing or reduction law is added."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/prefix-certified-substitution-reuse.json",JSON.stringify(out,null,2)+"\n");
console.log("PREFIX_CERTIFIED_SUBSTITUTION_REUSE "+JSON.stringify(out));
if(!out.promotable)process.exit(1);
