import { Kernel } from "./kernel-base.mjs";

// Retained execution consequence:
// 1) successful validation of the exact DAG node under the exact universe-parameter
//    set may be reused;
// 2) successful inference of the exact expression under the complete exact local
//    context may be reused.
//
// Only successes are cached. No failure, UNKNOWN, REJECT, conversion result, or
// declaration lookup is memoized. Declarations are immutable once installed, so
// a previously successful inference remains valid as the environment grows.

const retainedRun = Kernel.prototype.run;
const retainedValidate = Kernel.prototype.validate;
const retainedInfer = Kernel.prototype.infer;

function objectId(k,x) {
  k.__consequenceIds ??= new WeakMap();
  k.__consequenceNextId ??= 1;
  let id=k.__consequenceIds.get(x);
  if(id!==undefined) return id;
  id=k.__consequenceNextId++;
  k.__consequenceIds.set(x,id);
  return id;
}

function ctxKey(k,ctx) {
  if(!ctx?.length) return "";
  const parts=new Array(ctx.length);
  for(let i=0;i<ctx.length;i++) {
    const x=ctx[i];
    parts[i]=(x!==null&&(typeof x==="object"||typeof x==="function"))
      ?"o"+objectId(k,x)
      :typeof x+":"+String(x);
  }
  return parts.join(",");
}

function paramsKey(k) {
  return [...(k.params??[])].sort().join("\u0000");
}

Kernel.prototype.run = function(...args) {
  this.__consequenceValidation=new WeakMap();
  this.__consequenceInfer=new WeakMap();
  this.__consequenceIds=new WeakMap();
  this.__consequenceNextId=1;
  return retainedRun.apply(this,args);
};

Kernel.prototype.validate = function(root) {
  // Direct semantic tests may bypass run(); lazy initialization preserves identical behavior.
  this.__consequenceValidation ??= new WeakMap();
  const key=paramsKey(this);
  const work=[{kind:"visit",e:root}];

  while(work.length) {
    const f=work.pop(),e=f.e;
    if(!Array.isArray(e)) return retainedValidate.call(this,e);

    let keys=this.__consequenceValidation.get(e);
    if(!(keys instanceof Set)) {
      keys=new Set();
      this.__consequenceValidation.set(e,keys);
    }

    if(f.kind==="done") {
      keys.add(key);
      continue;
    }
    if(keys.has(key)) continue;

    if(["sort","var","const","nat","strlit"].includes(e[0])) {
      retainedValidate.call(this,e);
      keys.add(key);
      continue;
    }

    this.tick();
    if(typeof e[0]!=="string") this.reject("malformed-term");
    const arities={sort:2,var:2,const:2,nat:2,strlit:2,proj:4,pi:3,lam:3,app:3,let:4};
    if(!(e[0] in arities)) this.unknown("syntax:"+e[0]);
    if(e.length!==arities[e[0]] && !(e[0]==="const"&&e.length===3))
      this.reject("malformed-arity");

    work.push({kind:"done",e});
    if(e[0]==="proj") {
      this.need("projections");
      if(typeof e[1]!=="string"||!Number.isSafeInteger(e[2])||e[2]<0)
        this.reject("malformed-projection");
      work.push({kind:"visit",e:e[3]});
    } else {
      for(let i=e.length-1;i>=1;i--) work.push({kind:"visit",e:e[i]});
    }
  }
};

Kernel.prototype.infer = function(e,ctx=[]) {
  if(!Array.isArray(e)) return retainedInfer.call(this,e,ctx);

  // Direct semantic tests may bypass run(); cache identity state must still exist.
  this.__consequenceInfer ??= new WeakMap();
  this.__consequenceIds ??= new WeakMap();
  this.__consequenceNextId ??= 1;

  let byCtx=this.__consequenceInfer.get(e);
  if(!(byCtx instanceof Map)) {
    byCtx=new Map();
    this.__consequenceInfer.set(e,byCtx);
  }

  const key=ctxKey(this,ctx);
  if(byCtx.has(key)) return byCtx.get(key);

  const out=retainedInfer.call(this,e,ctx);
  byCtx.set(key,out);
  return out;
};
