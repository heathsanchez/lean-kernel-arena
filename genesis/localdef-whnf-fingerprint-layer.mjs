import {Kernel} from "./kernel-base.mjs";

// Diagnostic-only structural fingerprint for the local-definition fallback.
// No ticks, allocations, reductions, or semantic decisions are added here.
// The wrapper observes exact immutable terms and the active local context, then
// delegates once to the retained evaluator.
const p=Kernel.prototype;
const run0=p.run, whnf0=p.whnf, sub0=p.substitute;

function fresh(){
  return {
    whnfCalls:0,
    substituteCalls:0,
    whnfInputTag:Object.create(null),
    whnfHeadTag:Object.create(null),
    whnfArgBin:Object.create(null),
    localDefHeadCalls:0,
    localDefBareCalls:0,
    localDefAppCalls:0,
    localDefArgBin:Object.create(null),
    localDefIndexBin:Object.create(null),
    localDefCtxDepthBin:Object.create(null),
    localDefValueTag:Object.create(null),
    localDefTypeTag:Object.create(null),
    localDefOutputHeadTag:Object.create(null),
    localDefOutputArgBin:Object.create(null),
    localDefChanged:0,
    substituteRootTag:Object.create(null),
    substituteHeadTag:Object.create(null),
    substituteArgBin:Object.create(null),
    substituteDuringWhnf:0,
  };
}
function inc(obj,key){
  const k=String(key);obj[k]=(obj[k]??0)+1;
}
function bin(n){
  if(n<=0)return "0";
  if(n<=4)return String(n);
  if(n<=8)return "5-8";
  if(n<=16)return "9-16";
  if(n<=32)return "17-32";
  return "33+";
}
function tag(e){return Array.isArray(e)?String(e[0]):typeof e;}
function spine(e){
  let h=e,n=0;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  return {head:h,args:n};
}
function localDefInfo(k,s){
  if(k.localDefs!==true||!Array.isArray(s.head)||s.head[0]!=="var")return null;
  const i=s.head[1],ctx=k._activeCtx??[];
  if(!Number.isSafeInteger(i)||i<0||i>=ctx.length)return null;
  const entry=ctx[ctx.length-1-i];
  return entry?.__localDef===true?{index:i,ctxDepth:ctx.length,entry}:null;
}
function recordShape(stats,prefix,e){
  const s=spine(e);
  inc(stats[prefix+"Tag"],tag(e));
  inc(stats[prefix==="whnfInput"?"whnfHeadTag":"substituteHeadTag"],tag(s.head));
  inc(stats[prefix==="whnfInput"?"whnfArgBin":"substituteArgBin"],bin(s.args));
  return s;
}

p.run=function(...args){
  this.__localDefFingerprint=fresh();
  this.__localDefFingerprintWhnfDepth=0;
  return run0.apply(this,args);
};

p.whnf=function(e){
  const st=this.__localDefFingerprint??=fresh();
  st.whnfCalls++;
  const s=recordShape(st,"whnfInput",e);
  const info=localDefInfo(this,s);
  if(info){
    st.localDefHeadCalls++;
    if(s.args===0)st.localDefBareCalls++;else st.localDefAppCalls++;
    inc(st.localDefArgBin,bin(s.args));
    inc(st.localDefIndexBin,bin(info.index));
    inc(st.localDefCtxDepthBin,bin(info.ctxDepth));
    inc(st.localDefValueTag,tag(info.entry.value));
    inc(st.localDefTypeTag,tag(info.entry.type));
  }
  this.__localDefFingerprintWhnfDepth=(this.__localDefFingerprintWhnfDepth??0)+1;
  let out;
  try{out=whnf0.call(this,e);}
  finally{this.__localDefFingerprintWhnfDepth--;}
  if(info){
    const os=spine(out);
    inc(st.localDefOutputHeadTag,tag(os.head));
    inc(st.localDefOutputArgBin,bin(os.args));
    if(out!==e)st.localDefChanged++;
  }
  return out;
};

p.substitute=function(root,arg,depth=0){
  const st=this.__localDefFingerprint??=fresh();
  st.substituteCalls++;
  const s=spine(root);
  inc(st.substituteRootTag,tag(root));
  inc(st.substituteHeadTag,tag(s.head));
  inc(st.substituteArgBin,bin(s.args));
  if((this.__localDefFingerprintWhnfDepth??0)>0)st.substituteDuringWhnf++;
  return sub0.call(this,root,arg,depth);
};
