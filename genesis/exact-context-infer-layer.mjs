import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,infer0=p.infer;

function ensure(k){
  k.__exactInferMemo??=new WeakMap();
  k.__exactInferIds??=new WeakMap();
  k.__exactInferNextId??=1;
  k.__exactInferStats??={queries:0,hits:0,misses:0,stores:0,keyEntries:0};
}
function objId(k,x){
  let id=k.__exactInferIds.get(x);
  if(id===undefined){id=k.__exactInferNextId++;k.__exactInferIds.set(x,id);}
  return id;
}
function entryKey(k,x){
  if(Array.isArray(x)) return "a"+objId(k,x);
  if(x&&typeof x==="object"&&x.__localDef===true){
    const t=Array.isArray(x.type)?"a"+objId(k,x.type):typeof x.type+":"+JSON.stringify(x.type);
    const v=Array.isArray(x.value)?"a"+objId(k,x.value):typeof x.value+":"+JSON.stringify(x.value);
    return "d"+t+":"+v;
  }
  if(x&&typeof x==="object") return "o:"+JSON.stringify(x);
  return typeof x+":"+JSON.stringify(x);
}
function ctxKey(k,ctx){
  k.__exactInferStats.keyEntries+=ctx.length;
  let s="";
  for(let i=0;i<ctx.length;i++) s+=(i?"|":"")+entryKey(k,ctx[i]);
  return s;
}

p.run=function(...args){
  this.__exactInferMemo=new WeakMap();
  this.__exactInferIds=new WeakMap();
  this.__exactInferNextId=1;
  this.__exactInferStats={queries:0,hits:0,misses:0,stores:0,keyEntries:0};
  return run0.apply(this,args);
};

p.infer=function(e,ctx){
  ensure(this);
  if(!Array.isArray(e)||!Array.isArray(ctx)) return infer0.call(this,e,ctx);
  this.__exactInferStats.queries++;
  let byCtx=this.__exactInferMemo.get(e);
  if(!byCtx){byCtx=new Map();this.__exactInferMemo.set(e,byCtx);}
  const key=ctxKey(this,ctx);
  if(byCtx.has(key)){
    this.__exactInferStats.hits++;
    return byCtx.get(key);
  }
  this.__exactInferStats.misses++;
  const out=infer0.call(this,e,ctx);
  byCtx.set(key,out);this.__exactInferStats.stores++;
  return out;
};
