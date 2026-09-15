import { Kernel } from "./kernel-base.mjs";

// Retained consequence from the semantic-reuse separator: normalization is a
// deterministic successful consequence of an exact expression under one
// monotonic kernel run. Evaluate it with an explicit work stack while retaining
// successful results for every visited subtree, not just the top-level request.
// Weak identity keys preserve the exact term. Failures/frontiers are never cached.
const oldRun = Kernel.prototype.run;

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

function cacheSlot(kernel,e,ctxKey) {
  if(!Array.isArray(e)) return null;
  if(!kernel.localDefs) {
    return {
      has:()=>kernel._normalCache.has(e),
      get:()=>kernel._normalCache.get(e),
      set:v=>kernel._normalCache.set(e,v)
    };
  }
  let byCtx=kernel._normalCache.get(e);
  if(!(byCtx instanceof Map)) {
    byCtx=new Map();
    kernel._normalCache.set(e,byCtx);
  }
  return {
    has:()=>byCtx.has(ctxKey),
    get:()=>byCtx.get(ctxKey),
    set:v=>byCtx.set(ctxKey,v)
  };
}

Kernel.prototype.normal = function(root) {
  this._normalCache ??= new WeakMap();
  this._normalCtxIds ??= new WeakMap();
  this._nextNormalCtxId ??= 1;

  if(!Array.isArray(root)) return root;
  const ckey=this.localDefs ? contextKey(this,this._activeCtx??[]) : "";
  const work=[{kind:"visit",e:root}], vals=[];

  while(work.length) {
    const f=work.pop();
    if(f.kind==="build") {
      let out;
      if(f.tag==="proj") {
        out=this.make("proj",f.name,f.index,vals.pop());
      } else {
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
        out=this.make(f.tag,...xs);
      }
      f.slot.set(out);
      vals.push(out);
      continue;
    }

    const requested=f.e,slot=cacheSlot(this,requested,ckey);
    if(slot?.has()) {
      // Cache hits deliberately do not tick: the verified normalization
      // consequence has already been paid for and compiled.
      vals.push(slot.get());
      continue;
    }

    this.tick();
    const e=this.whnf(requested);

    // If weak-head reduction landed on an already normalized exact node, reuse
    // that consequence and cache it for the original request as well.
    if(e!==requested) {
      const reducedSlot=cacheSlot(this,e,ckey);
      if(reducedSlot?.has()) {
        const out=reducedSlot.get();
        slot?.set(out);
        vals.push(out);
        continue;
      }
    }

    if(["sort","var","const","nat","strlit"].includes(e[0])) {
      slot?.set(e);
      if(e!==requested) cacheSlot(this,e,ckey)?.set(e);
      vals.push(e);
      continue;
    }

    if(e[0]==="proj") {
      work.push({kind:"build",tag:"proj",name:e[1],index:e[2],slot});
      work.push({kind:"visit",e:e[3]});
      continue;
    }

    work.push({kind:"build",tag:e[0],n:e.length-1,slot});
    for(let i=e.length-1;i>=1;i--) work.push({kind:"visit",e:e[i]});
  }

  return vals.pop();
};
