import {Kernel} from "./kernel-base.mjs";

// Experimental exact structural WHNF consequence cache.
//
// The retained identity cache only recognizes the same array object. Giant
// Prelude checking reconstructs the same small WHNF states under fresh object
// identities hundreds of thousands of times. This layer keys only small
// immutable ordinary terms by their exact JSON syntax. A cache entry is stored
// only after WHNF succeeds. Local-definition execution is excluded because
// WHNF(var) depends on the active local context.
//
// Environment soundness: declarations are installed monotonically and never
// redefined. If a referenced constant is unavailable, WHNF throws and nothing
// is cached. Therefore every successful exact structural consequence remains
// valid for the rest of that run.
const p=Kernel.prototype,run0=p.run,whnf0=p.whnf;
const MAX_KEY_BYTES=65536;

p.run=function(...args){
  this.__structWhnf=new Map();
  this.__structWhnfKeys=new WeakMap();
  this.__structWhnfHits=0;
  this.__structWhnfStores=0;
  this.__structWhnfSkipped=0;
  return run0.apply(this,args);
};

function keyOf(k,e){
  k.__structWhnfKeys??=new WeakMap();
  let x=k.__structWhnfKeys.get(e);
  if(x!==undefined)return x;
  x=JSON.stringify(e);
  if(x.length>MAX_KEY_BYTES)x=null;
  k.__structWhnfKeys.set(e,x);
  return x;
}

p.whnf=function(e){
  if(this.localDefs===true||!Array.isArray(e))return whnf0.call(this,e);
  this.__structWhnf??=new Map();
  const key=keyOf(this,e);
  if(key===null){
    this.__structWhnfSkipped=(this.__structWhnfSkipped??0)+1;
    return whnf0.call(this,e);
  }
  if(this.__structWhnf.has(key)){
    this.__structWhnfHits=(this.__structWhnfHits??0)+1;
    return this.__structWhnf.get(key);
  }
  const out=whnf0.call(this,e);
  this.__structWhnf.set(key,out);
  this.__structWhnfStores=(this.__structWhnfStores??0)+1;
  return out;
};
