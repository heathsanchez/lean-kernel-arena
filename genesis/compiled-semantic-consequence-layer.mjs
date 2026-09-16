import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype;
const run0=p.run,whnf0=p.whnf,normal0=p.normal,same0=p.same,proofType0=p.proofType,equal0=p.equal,inst0=p.instantiateDeclaration;
const NULL=Symbol("null-proof-type");

function reset(k){
  k.__semWhnf=new WeakMap();
  k.__semNormal=new WeakMap();
  k.__semSame=new WeakMap();
  k.__semProofType=new WeakMap();
  k.__semEqual=new WeakMap();
  k.__semInst=new WeakMap();
  k.__semObjIds=new WeakMap();
  k.__semNextObjId=1;
  k.__semStats={whnfHits:0,whnfStores:0,normalHits:0,normalStores:0,sameHits:0,sameStores:0,
    proofHits:0,proofStores:0,equalHits:0,equalStores:0,instHits:0,instStores:0};
}
function ensure(k){if(!k.__semStats)reset(k);}
function objId(k,x){
  if(x===null)return "null";
  if(typeof x!=="object")return typeof x+":"+String(x);
  let id=k.__semObjIds.get(x);
  if(id===undefined){id=k.__semNextObjId++;k.__semObjIds.set(x,id);}
  return String(id);
}
function ctxKey(k,ctx){
  if(!ctx?.length)return "";
  return ctx.map(x=>objId(k,x)).join(",");
}
function pairMap(root,a){
  let m=root.get(a);if(!m){m=new WeakMap();root.set(a,m);}return m;
}
function ctxPairMap(k,root,a,b){
  let byB=root.get(a);if(!byB){byB=new WeakMap();root.set(a,byB);}
  let byCtx=byB.get(b);if(!byCtx){byCtx=new Set();byB.set(b,byCtx);}
  return byCtx;
}

p.run=function(...args){reset(this);return run0.apply(this,args);};

p.whnf=function(e){
  ensure(this);
  if(this.localDefs===true||!Array.isArray(e))return whnf0.call(this,e);
  const old=this.__semWhnf.get(e);
  if(old!==undefined){this.__semStats.whnfHits++;return old;}
  const out=whnf0.call(this,e);
  this.__semWhnf.set(e,out);this.__semStats.whnfStores++;
  return out;
};

p.normal=function(e){
  ensure(this);
  if(this.localDefs===true||!Array.isArray(e))return normal0.call(this,e);
  const old=this.__semNormal.get(e);
  if(old!==undefined){this.__semStats.normalHits++;return old;}
  const out=normal0.call(this,e);
  this.__semNormal.set(e,out);this.__semStats.normalStores++;
  return out;
};

p.same=function(a,b){
  ensure(this);
  if(a===b)return true;
  if(!Array.isArray(a)||!Array.isArray(b))return same0.call(this,a,b);
  const m=pairMap(this.__semSame,a);
  if(m.has(b)){this.__semStats.sameHits++;return m.get(b);}
  const out=same0.call(this,a,b);
  m.set(b,out);pairMap(this.__semSame,b).set(a,out);this.__semStats.sameStores++;
  return out;
};

p.proofType=function(e,ctx=[]){
  ensure(this);
  if(this.localDefs===true||!Array.isArray(e))return proofType0.call(this,e,ctx);
  let m=this.__semProofType.get(e);if(!m){m=new Map();this.__semProofType.set(e,m);}
  const key=ctxKey(this,ctx);
  if(m.has(key)){this.__semStats.proofHits++;const v=m.get(key);return v===NULL?null:v;}
  const out=proofType0.call(this,e,ctx);
  m.set(key,out===null?NULL:out);this.__semStats.proofStores++;
  return out;
};

p.equal=function(a,b,ctx=[]){
  ensure(this);
  if(this.localDefs===true||!Array.isArray(a)||!Array.isArray(b))return equal0.call(this,a,b,ctx);
  const key=ctxKey(this,ctx),m=ctxPairMap(this,this.__semEqual,a,b);
  if(m.has(key)){this.__semStats.equalHits++;return;}
  const out=equal0.call(this,a,b,ctx);
  m.add(key);ctxPairMap(this,this.__semEqual,b,a).add(key);this.__semStats.equalStores++;
  return out;
};

p.instantiateDeclaration=function(ref,term){
  ensure(this);
  if(!Array.isArray(ref)||!Array.isArray(term))return inst0.call(this,ref,term);
  let m=this.__semInst.get(ref);if(!m){m=new WeakMap();this.__semInst.set(ref,m);}
  if(m.has(term)){this.__semStats.instHits++;return m.get(term);}
  const out=inst0.call(this,ref,term);
  m.set(term,out);this.__semStats.instStores++;
  return out;
};
