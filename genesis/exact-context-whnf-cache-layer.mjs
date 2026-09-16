import {Kernel} from "./kernel-base.mjs";

// Exact successful WHNF consequence reuse.
// Key = immutable term object identity + exact active local-context entry
// identities + execution mode. Environment declarations are monotonic within a
// run and duplicate names are rejected, so a successful reduction cannot be
// invalidated later in that run. Exceptions/frontiers are never cached.
const p=Kernel.prototype,run0=p.run,whnf0=p.whnf;

function reset(k){
  k.__whnfExact=new WeakMap();
  k.__whnfCtxIds=new WeakMap();
  k.__whnfNextCtxId=1;
  k.__whnfExactHits=0;
  k.__whnfExactStores=0;
}
function id(k,x){
  if(x===null||((typeof x!=="object")&&(typeof x!=="function")))return typeof x+":"+String(x);
  let v=k.__whnfCtxIds.get(x);
  if(v===undefined){v=k.__whnfNextCtxId++;k.__whnfCtxIds.set(x,v);}
  return "o"+v;
}
function key(k){
  const ctx=k.localDefs===true?(k._activeCtx??[]):[];
  const c=ctx.length?ctx.map(x=>id(k,x)).join(","):"";
  return (k._fullStackSafe===true?"F":"R")+"|"+(k.__whnfReentryStackSafe===true?"E":"N")+"|"+c;
}
function mapFor(k,e){
  k.__whnfExact??=new WeakMap();
  let m=k.__whnfExact.get(e);
  if(!m){m=new Map();k.__whnfExact.set(e,m);}
  return m;
}

p.run=function(...args){reset(this);return run0.apply(this,args);};
p.whnf=function(e){
  if(!Array.isArray(e))return whnf0.call(this,e);
  if(!this.__whnfCtxIds)reset(this);
  const m=mapFor(this,e),k=key(this);
  if(m.has(k)){
    this.__whnfExactHits++;
    return m.get(k);
  }
  const out=whnf0.call(this,e);
  m.set(k,out);
  this.__whnfExactStores++;
  return out;
};

export const exactContextWhnfCacheInstalled=true;
