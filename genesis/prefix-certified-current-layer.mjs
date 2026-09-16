import {Kernel} from "./kernel-base.mjs";
import "./recursor-prefix-cache-layer.mjs";

// Experimental execution layer only. Import this module dynamically *after*
// production.mjs so it wraps the exact current production substitution engine.
// It adds no proof rule: binder independence is certified by the retained
// lowerBound transform; dependent results are reused only under exact immutable
// root/argument identity and exact depth.
const p=Kernel.prototype;
const run0=p.run,sub0=p.substitute,lower0=p.lowerBound;

function ensure(k){k.__prefixCertifiedIndependent??=new WeakMap();k.__prefixCertifiedExact??=new WeakMap();}
function indepMap(k,root){
  let m=k.__prefixCertifiedIndependent.get(root);
  if(!m){m=new Map();k.__prefixCertifiedIndependent.set(root,m);}
  return m;
}
function exactMap(k,root,arg){
  let byArg=k.__prefixCertifiedExact.get(root);
  if(!byArg){byArg=new WeakMap();k.__prefixCertifiedExact.set(root,byArg);}
  let m=byArg.get(arg);
  if(!m){m=new Map();byArg.set(arg,m);}
  return m;
}
function reset(k){
  k.__prefixCertifiedIndependent=new WeakMap();
  k.__prefixCertifiedExact=new WeakMap();
  k.__prefixCertifiedStats={queries:0,independentHits:0,independentStores:0,dependentStores:0,exactHits:0,exactStores:0};
}

p.run=function(...xs){reset(this);return run0.apply(this,xs);};
p.substitute=function(root,arg,depth=0){
  if(!Array.isArray(root)||!Array.isArray(arg))return sub0.call(this,root,arg,depth);
  ensure(this);this.__prefixCertifiedStats??=reset(this);this.__prefixCertifiedStats.queries++;
  const indep=indepMap(this,root);
  if(indep.has(depth)){
    const entry=indep.get(depth);
    if(entry.absent){this.__prefixCertifiedStats.independentHits++;return entry.out;}
  }else{
    const out=lower0.call(this,root,depth);
    if(out!==null){
      indep.set(depth,{absent:true,out});this.__prefixCertifiedStats.independentStores++;return out;
    }
    indep.set(depth,{absent:false});this.__prefixCertifiedStats.dependentStores++;
  }
  const ex=exactMap(this,root,arg);
  if(ex.has(depth)){this.__prefixCertifiedStats.exactHits++;return ex.get(depth);}
  const out=sub0.call(this,root,arg,depth);
  ex.set(depth,out);this.__prefixCertifiedStats.exactStores++;return out;
};

export const prefixCertifiedInstalled=true;
