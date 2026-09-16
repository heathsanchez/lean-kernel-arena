import {Kernel} from "./kernel-base.mjs";

// Exact retained representation consequences:
// 1. Reusing an already-built node with the identical tag, scalar values and
//    child object identities performs no new semantic construction.
// 2. Decomposing the identical immutable application term reuses its exact spine.
// Misses fall through to the retained implementations unchanged.
const p=Kernel.prototype,run0=p.run,make0=p.make,getApp0=p.getApp;

function objId(k,x){
  k.__compiledObjIds??=new WeakMap();
  k.__compiledNextObjId??=1;
  let id=k.__compiledObjIds.get(x);
  if(id!==undefined)return id;
  id=k.__compiledNextObjId++;
  k.__compiledObjIds.set(x,id);
  return id;
}
function scalarKey(x){
  if(typeof x==="number")return "n:"+x;
  if(typeof x==="string")return "s:"+x;
  if(typeof x==="boolean")return "b:"+(x?1:0);
  if(x===null)return "null";
  if(x===undefined)return "u";
  return typeof x+":"+String(x);
}
function keyOf(k,xs){
  let out="";
  for(const x of xs){
    out+="|"+(Array.isArray(x)?"o:"+objId(k,x):scalarKey(x));
  }
  return out;
}

p.run=function(...args){
  this.__compiledNodeReuse=new Map();
  this.__compiledSpines=new WeakMap();
  this.__compiledObjIds=new WeakMap();
  this.__compiledNextObjId=1;
  this.__compiledNodeHits=0;
  this.__compiledSpineHits=0;
  return run0.apply(this,args);
};

p.make=function(...xs){
  this.__compiledNodeReuse??=new Map();
  const key=keyOf(this,xs);
  if(this.__compiledNodeReuse.has(key)){
    this.__compiledNodeHits=(this.__compiledNodeHits??0)+1;
    return this.__compiledNodeReuse.get(key);
  }
  const out=make0.apply(this,xs);
  this.__compiledNodeReuse.set(key,out);
  objId(this,out);
  return out;
};

p.getApp=function(e){
  if(!Array.isArray(e))return getApp0.call(this,e);
  this.__compiledSpines??=new WeakMap();
  const hit=this.__compiledSpines.get(e);
  if(hit!==undefined){
    this.__compiledSpineHits=(this.__compiledSpineHits??0)+1;
    return hit;
  }
  const out=getApp0.call(this,e);
  this.__compiledSpines.set(e,out);
  return out;
};
