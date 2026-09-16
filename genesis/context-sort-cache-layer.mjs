import {Kernel} from "./kernel-base.mjs";

// Pure execution consequence parallel to the inference cache: successful sortOf
// is deterministic in (expression object, typing context). Conservative object
// identity keys avoid structural assumptions; LocalDefKernel is bypassed.
const p=Kernel.prototype,sort0=p.sortOf,run0=p.run;
function reset(k){k.__sortCache=new WeakMap();k.__sortObjIds=new WeakMap();k.__sortNextObjId=1;k.__sortCacheStats={calls:0,hits:0,stores:0};}
function ensure(k){if(!k.__sortCache)reset(k);}
function objId(k,x){if(x===null)return "null";if(typeof x!=="object")return typeof x+":"+String(x);let id=k.__sortObjIds.get(x);if(id===undefined){id=k.__sortNextObjId++;k.__sortObjIds.set(x,id);}return String(id);}
function ctxKey(k,ctx){return ctx?.length?ctx.map(x=>objId(k,x)).join(","):"";}
p.run=function(...xs){reset(this);return run0.apply(this,xs);};
p.sortOf=function(e,ctx=[]){
  ensure(this);const st=this.__sortCacheStats;st.calls++;
  if(this.localDefs===true||!Array.isArray(e))return sort0.call(this,e,ctx);
  let byCtx=this.__sortCache.get(e);if(!byCtx){byCtx=new Map();this.__sortCache.set(e,byCtx);}
  const key=ctxKey(this,ctx);if(byCtx.has(key)){st.hits++;return byCtx.get(key);}
  const out=sort0.call(this,e,ctx);byCtx.set(key,out);st.stores++;return out;
};
