import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run;

function ensure(k){
  k._termCons??=new Map();
  k._termObjectIds??=new WeakMap();
  k._nextTermObjectId??=1;
  k.__makeReuseStats??={hits:0,misses:0};
}
function objectId(k,x){
  ensure(k);
  let id=k._termObjectIds.get(x);
  if(id!==undefined)return id;
  id=k._nextTermObjectId++;
  k._termObjectIds.set(x,id);
  return id;
}

p.run=function(...args){
  this.__makeReuseStats={hits:0,misses:0};
  return run0.apply(this,args);
};

p.make=function(...xs){
  ensure(this);
  const key=JSON.stringify(xs.map(x=>
    Array.isArray(x)?["array",objectId(this,x)]:[typeof x,x]
  ));
  const old=this._termCons.get(key);
  if(old!==undefined){
    this.__makeReuseStats.hits++;
    return old;
  }
  this.__makeReuseStats.misses++;
  this.tick();
  this.allocations++;
  this._termCons.set(key,xs);
  objectId(this,xs);
  return xs;
};
