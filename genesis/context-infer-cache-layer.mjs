import {Kernel} from "./kernel-base.mjs";

// Pure execution consequence: successful inference is a deterministic function
// of (expression object, local typing context) for the retained base kernel.
// Cache only successful results, reset per checker run, and bypass LocalDefKernel
// because its context entries contain local values with separate reduction semantics.
const p=Kernel.prototype,infer0=p.infer,run0=p.run;

function reset(k){
  k.__inferCache=new WeakMap();
  k.__inferObjIds=new WeakMap();
  k.__inferNextObjId=1;
  k.__inferCacheStats={calls:0,hits:0,stores:0};
}
function ensure(k){if(!k.__inferCache)reset(k);}
function objId(k,x){
  if(x===null)return "null";
  if(typeof x!=="object")return typeof x+":"+String(x);
  let id=k.__inferObjIds.get(x);
  if(id===undefined){id=k.__inferNextObjId++;k.__inferObjIds.set(x,id);}
  return String(id);
}
function ctxKey(k,ctx){
  if(!ctx?.length)return "";
  return ctx.map(x=>objId(k,x)).join(",");
}

p.run=function(...xs){reset(this);return run0.apply(this,xs);};
p.infer=function(e,ctx=[]){
  ensure(this);
  const st=this.__inferCacheStats;st.calls++;
  if(this.localDefs===true||!Array.isArray(e))return infer0.call(this,e,ctx);
  let byCtx=this.__inferCache.get(e);
  if(!byCtx){byCtx=new Map();this.__inferCache.set(e,byCtx);}
  const key=ctxKey(this,ctx);
  if(byCtx.has(key)){st.hits++;return byCtx.get(key);}
  const out=infer0.call(this,e,ctx);
  byCtx.set(key,out);st.stores++;
  return out;
};
