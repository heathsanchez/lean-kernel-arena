import {Kernel} from "./kernel-base.mjs";

// Experimental exact structural normalization consequence cache.
// Successful normal forms of exact immutable terms are retained by exact JSON
// syntax within one monotone kernel run. Failures/UNKNOWNs are never cached.
// Local-definition mode is excluded because normalization of variables depends
// on the active local context.
const p=Kernel.prototype,run0=p.run,normal0=p.normal;
const MAX_KEY_BYTES=65536;

p.run=function(...args){
  this.__structNormal=new Map();
  this.__structNormalKeys=new WeakMap();
  this.__structNormalHits=0;
  this.__structNormalStores=0;
  this.__structNormalSkipped=0;
  return run0.apply(this,args);
};

function keyOf(k,e){
  k.__structNormalKeys??=new WeakMap();
  let x=k.__structNormalKeys.get(e);
  if(x!==undefined)return x;
  x=JSON.stringify(e);
  if(x.length>MAX_KEY_BYTES)x=null;
  k.__structNormalKeys.set(e,x);
  return x;
}

p.normal=function(e){
  if(this.localDefs===true||!Array.isArray(e))return normal0.call(this,e);
  this.__structNormal??=new Map();
  const key=keyOf(this,e);
  if(key===null){
    this.__structNormalSkipped=(this.__structNormalSkipped??0)+1;
    return normal0.call(this,e);
  }
  if(this.__structNormal.has(key)){
    this.__structNormalHits=(this.__structNormalHits??0)+1;
    return this.__structNormal.get(key);
  }
  const out=normal0.call(this,e);
  this.__structNormal.set(key,out);
  this.__structNormalStores=(this.__structNormalStores??0)+1;
  return out;
};
