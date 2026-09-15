import { Kernel } from "./kernel-base.mjs";

// Retained consequence from the semantic-reuse separator: normalization is a
// deterministic successful consequence of an exact expression under one
// monotonic kernel run. Cache successes only; failures/frontiers are never
// retained. Weak identity keys preserve the exact term, not an approximation.
//
// A cache hit deliberately does not tick: the separator established that the
// expensive normalization consequence has already been paid for and compiled.
// Re-charging semantic work on reuse erased the verified capability gain.
//
// The retained checker has no local definitions, so expression identity is a
// complete key there. The optional local-definition fallback can normalize the
// same de-Bruijn expression differently under different exact local contexts;
// only that mode adds the complete context identity sequence to the key.
const oldRun = Kernel.prototype.run;
const oldNormal = Kernel.prototype.normal;

Kernel.prototype.run = function(...args) {
  this._normalCache = new WeakMap();
  this._normalCtxIds = new WeakMap();
  this._nextNormalCtxId = 1;
  return oldRun.apply(this,args);
};

function contextKey(kernel,ctx) {
  const parts=[];
  for(const entry of ctx) {
    if(entry!==null && (typeof entry==="object" || typeof entry==="function")) {
      let id=kernel._normalCtxIds.get(entry);
      if(id===undefined) {
        id=kernel._nextNormalCtxId++;
        kernel._normalCtxIds.set(entry,id);
      }
      parts.push(id);
    } else {
      parts.push(typeof entry+":"+String(entry));
    }
  }
  return parts.join(",");
}

Kernel.prototype.normal = function(e) {
  this._normalCache ??= new WeakMap();
  if(!Array.isArray(e)) return oldNormal.call(this,e);

  if(!this.localDefs) {
    if(this._normalCache.has(e)) return this._normalCache.get(e);
    const out=oldNormal.call(this,e);
    this._normalCache.set(e,out);
    return out;
  }

  let byCtx=this._normalCache.get(e);
  if(!(byCtx instanceof Map)) {
    byCtx=new Map();
    this._normalCache.set(e,byCtx);
  }
  const key=contextKey(this,this._activeCtx??[]);
  if(byCtx.has(key)) return byCtx.get(key);
  const out=oldNormal.call(this,e);
  byCtx.set(key,out);
  return out;
};
