import { Kernel } from "./kernel-base.mjs";

// Retained execution consequences from the LocalDef continuation separators.
//
// The fast local-definition fallback keeps exactly the same variable lookup,
// local-definition context, typing, conversion, substitution and capability
// rules. Nested app/lambda/let inference uses an explicit continuation stack.
//
// Successful inference is also memoized at each exact continuation-machine DAG
// node under the complete exact local context. This is execution compilation
// only: failures are never cached and semantic rules are unchanged.
//
// This module is imported after consequence-cache.mjs so it wraps the exact
// retained inference stack replayed on all 188 Arena cases.

const retainedRun=Kernel.prototype.run;
const retainedInfer=Kernel.prototype.infer;

function objectId(k,x) {
  k.__localMachineCtxIds ??= new WeakMap();
  k.__localMachineNextId ??= 1;
  let id=k.__localMachineCtxIds.get(x);
  if(id!==undefined) return id;
  id=k.__localMachineNextId++;
  k.__localMachineCtxIds.set(x,id);
  return id;
}

function ctxKey(k,ctx) {
  if(!ctx?.length) return "";
  return ctx.map(x=>(x!==null&&(typeof x==="object"||typeof x==="function"))
    ?"o"+objectId(k,x)
    :typeof x+":"+String(x)).join(",");
}

function scoped(k,ctx,fn) {
  return typeof k.withCtx==="function" ? k.withCtx(ctx,fn) : fn();
}

function cacheGet(k,e,ctx) {
  if(!Array.isArray(e)) return {hit:false,key:null,map:null};
  k.__localMachineInfer ??= new WeakMap();
  let byCtx=k.__localMachineInfer.get(e);
  if(!(byCtx instanceof Map)) {
    byCtx=new Map();
    k.__localMachineInfer.set(e,byCtx);
  }
  const key=ctxKey(k,ctx);
  return byCtx.has(key)
    ? {hit:true,value:byCtx.get(key),key,map:byCtx}
    : {hit:false,key,map:byCtx};
}

function localContinuationInfer(root,rootCtx) {
  let e=root,ctx=rootCtx,value,returning=false;
  const kont=[];

  while(true) {
    if(!returning) {
      const memo=cacheGet(this,e,ctx);
      if(memo.hit) {
        value=memo.value;
        returning=true;
        continue;
      }
      if(memo.map) kont.push({kind:"memo",map:memo.map,key:memo.key});

      if(Array.isArray(e) && e[0]==="app") {
        this.tick(); this.need("application");
        kont.push({kind:"app-fn",arg:e[2],ctx});
        e=e[1];
        continue;
      }

      if(Array.isArray(e) && e[0]==="lam") {
        this.tick(); this.need("binders");
        scoped(this,ctx,()=>this.sortOf(e[1],ctx));
        kont.push({kind:"lam",domain:e[1],ctx});
        ctx=[...ctx,e[1]];
        e=e[2];
        continue;
      }

      if(Array.isArray(e) && e[0]==="let") {
        this.tick(); this.need("reduction");
        scoped(this,ctx,()=>this.sortOf(e[1],ctx));
        kont.push({kind:"let-value",type:e[1],valueTerm:e[2],body:e[3],ctx});
        e=e[2];
        continue;
      }

      if(Array.isArray(e) && e[0]==="var") {
        this.tick(); this.need("binders");
        if(e[1]>=ctx.length) this.reject("unbound-variable");
        const entry=ctx[ctx.length-1-e[1]];
        const ty=entry?.__localDef===true?entry.type:entry;
        value=this.shift(ty,e[1]+1);
        returning=true;
        continue;
      }

      value=scoped(this,ctx,()=>retainedInfer.call(this,e,ctx));
      returning=true;
      continue;
    }

    if(!kont.length) return value;
    const k=kont.pop();

    if(k.kind==="memo") {
      k.map.set(k.key,value);
      continue;
    }

    if(k.kind==="lam") {
      value=this.make("pi",k.domain,value);
      ctx=k.ctx;
      continue;
    }

    if(k.kind==="app-fn") {
      const fty=scoped(this,k.ctx,()=>this.whnf(value));
      if(fty[0]!=="pi") this.reject("not-a-function");
      kont.push({kind:"app-arg",fty,arg:k.arg,ctx:k.ctx});
      e=k.arg; ctx=k.ctx; returning=false;
      continue;
    }

    if(k.kind==="app-arg") {
      scoped(this,k.ctx,()=>this.equal(value,k.fty[1],k.ctx));
      value=this.substitute(k.fty[2],k.arg);
      ctx=k.ctx;
      continue;
    }

    if(k.kind==="let-value") {
      scoped(this,k.ctx,()=>this.equal(value,k.type,k.ctx));
      const entry={__localDef:true,type:k.type,value:k.valueTerm};
      kont.push({kind:"let-body",valueTerm:k.valueTerm,ctx:k.ctx});
      ctx=[...k.ctx,entry];
      e=k.body; returning=false;
      continue;
    }

    if(k.kind==="let-body") {
      value=this.substitute(value,k.valueTerm);
      ctx=k.ctx;
      continue;
    }

    throw new Error("unknown local continuation frame");
  }
}

Kernel.prototype.run=function(...args) {
  this.__localMachineInfer=new WeakMap();
  this.__localMachineCtxIds=new WeakMap();
  this.__localMachineNextId=1;
  return retainedRun.apply(this,args);
};

Kernel.prototype.infer=function(e,ctx=[]) {
  if(this.localDefs!==true) return retainedInfer.call(this,e,ctx);

  // LocalDefKernel itself handles root var/let before calling super.infer.
  // Own nested app/lam control flow here; all other forms keep the retained path.
  if(!Array.isArray(e) || !["app","lam"].includes(e[0]))
    return retainedInfer.call(this,e,ctx);

  return localContinuationInfer.call(this,e,ctx);
};
