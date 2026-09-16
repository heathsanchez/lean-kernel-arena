import {Kernel} from "./kernel-base.mjs";

// Exact one-run WHNF consequence cache for immutable ordinary terms.
// Local-definition execution is excluded because WHNF(var) depends on active
// local definition context. Only successful retained WHNF results are stored.
const p=Kernel.prototype,run0=p.run,whnf0=p.whnf;

p.run=function(...args){
  this.__whnfExact=new WeakMap();
  this.__whnfExactHits=0;
  this.__whnfExactStores=0;
  return run0.apply(this,args);
};

p.whnf=function(e){
  if(this.localDefs===true||!Array.isArray(e))return whnf0.call(this,e);
  this.__whnfExact??=new WeakMap();
  const old=this.__whnfExact.get(e);
  if(old!==undefined){
    this.__whnfExactHits=(this.__whnfExactHits??0)+1;
    return old;
  }
  const out=whnf0.call(this,e);
  this.__whnfExact.set(e,out);
  this.__whnfExactStores=(this.__whnfExactStores??0)+1;
  return out;
};
