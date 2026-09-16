import {Kernel} from "./kernel-base.mjs";

// Exact execution compilation for lowerBound(e, cut).
// Terms are immutable during a kernel run. Cache a completed transform, including
// the exact null obstruction, under object identity + exact cutoff. Exceptions
// are never cached. Recursive calls re-enter this wrapper, so shared DAG children
// also acquire exact certificates after their first retained traversal.
const p=Kernel.prototype,run0=p.run,lower0=p.lowerBound;

function reset(k){
  k.__lowerBoundExact=new WeakMap();
  k.__lowerBoundExactHits=0;
  k.__lowerBoundExactStores=0;
  k.__lowerBoundExactNullHits=0;
}
function mapFor(k,e){
  k.__lowerBoundExact??=new WeakMap();
  let m=k.__lowerBoundExact.get(e);
  if(!m){m=new Map();k.__lowerBoundExact.set(e,m);}
  return m;
}

p.run=function(...args){reset(this);return run0.apply(this,args);};
p.lowerBound=function(e,cut=0){
  if(!Array.isArray(e))return lower0.call(this,e,cut);
  const m=mapFor(this,e);
  if(m.has(cut)){
    this.__lowerBoundExactHits=(this.__lowerBoundExactHits??0)+1;
    const out=m.get(cut);
    if(out===null)this.__lowerBoundExactNullHits=(this.__lowerBoundExactNullHits??0)+1;
    return out;
  }
  const out=lower0.call(this,e,cut);
  m.set(cut,out);
  this.__lowerBoundExactStores=(this.__lowerBoundExactStores??0)+1;
  return out;
};

export const exactLowerBoundCacheInstalled=true;
