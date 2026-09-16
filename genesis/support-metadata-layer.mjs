import {Kernel} from "./kernel-base.mjs";

// Exact execution-only loose-variable support metadata.
//
// support(e) is max loose de-Bruijn index + 1 relative to e. This is the
// same structural consequence already computed lazily by
// exact-binder-transport-layer.mjs. Keeping it on immutable term nodes moves
// repeated discovery out of substitution without adding any semantic rule.
const p=Kernel.prototype,run0=p.run,validate0=p.validate,make0=p.make;

function ensure(k){
  k.__support??=new WeakMap();
  k.__supportStats??={seedVisits:0,makeKnown:0,makeUnknown:0};
}

function known(k,e){
  if(!Array.isArray(e))return 0;
  return k.__support.get(e);
}

function derive(k,e){
  if(!Array.isArray(e))return 0;
  ensure(k);
  const cached=k.__support.get(e);
  if(cached!==undefined)return cached;

  let out;
  switch(e[0]){
    case "sort": case "const": case "nat": case "strlit":
      out=0;break;
    case "var":
      if(Number.isSafeInteger(e[1])&&e[1]>=0)out=e[1]+1;
      break;
    case "app":{
      const a=known(k,e[1]),b=known(k,e[2]);
      if(a!==undefined&&b!==undefined)out=Math.max(a,b);
      break;
    }
    case "proj":{
      const x=known(k,e[3]);
      if(x!==undefined)out=x;
      break;
    }
    case "pi": case "lam":{
      const a=known(k,e[1]),b=known(k,e[2]);
      if(a!==undefined&&b!==undefined)out=Math.max(a,Math.max(0,b-1));
      break;
    }
    case "let":{
      const a=known(k,e[1]),v=known(k,e[2]),b=known(k,e[3]);
      if(a!==undefined&&v!==undefined&&b!==undefined)
        out=Math.max(a,v,Math.max(0,b-1));
      break;
    }
  }
  if(out!==undefined)k.__support.set(e,out);
  return out;
}

function seed(k,root){
  ensure(k);
  if(!Array.isArray(root)||k.__support.has(root))return;
  const work=[{e:root,post:false}];
  while(work.length){
    const f=work.pop(),e=f.e;
    if(!Array.isArray(e)||k.__support.has(e))continue;
    if(f.post){
      derive(k,e);
      k.__supportStats.seedVisits++;
      continue;
    }
    work.push({e,post:true});
    switch(e[0]){
      case "app":
        work.push({e:e[2],post:false},{e:e[1],post:false});break;
      case "proj":
        work.push({e:e[3],post:false});break;
      case "pi": case "lam":
        work.push({e:e[2],post:false},{e:e[1],post:false});break;
      case "let":
        work.push({e:e[3],post:false},{e:e[2],post:false},{e:e[1],post:false});break;
    }
  }
}

p.run=function(...args){
  this.__support=new WeakMap();
  this.__supportStats={seedVisits:0,makeKnown:0,makeUnknown:0};
  return run0.apply(this,args);
};

p.validate=function(root){
  const out=validate0.call(this,root);
  seed(this,root);
  return out;
};

p.make=function(...xs){
  ensure(this);
  const out=make0.apply(this,xs);
  if(Array.isArray(out)){
    const support=derive(this,out);
    if(support===undefined)this.__supportStats.makeUnknown++;
    else this.__supportStats.makeKnown++;
  }
  return out;
};

export {derive as deriveSupport,seed as seedSupport};
