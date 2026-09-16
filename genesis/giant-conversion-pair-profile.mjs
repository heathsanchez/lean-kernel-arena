import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function count(root){
  let n=0,bytes=0; const st=[root],seen=new Set();
  while(st.length){
    const e=st.pop(); if(!Array.isArray(e)||seen.has(e))continue;
    seen.add(e);n++;bytes+=JSON.stringify(e).length;
    for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))st.push(e[i]);
  }
  return {nodes:n,aggregate_bytes:bytes};
}
function head(e){let h=e,args=0;while(Array.isArray(h)&&h[0]==="app"){args++;h=h[1];}
  return Array.isArray(h)?{tag:h[0],name:h[0]==="const"?h[1]:null,args}:{tag:typeof h,args};}
function firstDiff(a,b,path="$",depth=0){
  if(a===b)return null;
  if(depth>2000)return {path,kind:"depth"};
  if(Array.isArray(a)!==Array.isArray(b))return {path,kind:"array",a:typeof a,b:typeof b};
  if(!Array.isArray(a))return {path,kind:"scalar",a,b};
  if(a.length!==b.length)return {path:path+".length",kind:"length",a:a.length,b:b.length,ah:head(a),bh:head(b)};
  for(let i=0;i<a.length;i++){
    const d=firstDiff(a[i],b[i],path+"["+i+"]",depth+1);if(d)return d;
  }
  return null;
}
function commonIdentity(a,b){
  let same=0,total=0,stack=[[a,b]];
  while(stack.length){
    const [x,y]=stack.pop();
    if(!Array.isArray(x)||!Array.isArray(y))continue;
    total++;
    if(x===y){same++;continue;}
    const m=Math.min(x.length,y.length);
    for(let i=1;i<m;i++) if(Array.isArray(x[i])&&Array.isArray(y[i])) stack.push([x[i],y[i]]);
  }
  return {same,total,share:total?same/total:0};
}

const p=K.Kernel.prototype,eq0=p.equal,run0=p.run;
p.run=function(...xs){this.__largestConv=null;return run0.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
  try{return eq0.call(this,a,b,ctx);}
  catch(e){
    if(e?.message==="conversion-frontier"){
      const ab=JSON.stringify(a),bb=JSON.stringify(b),size=ab.length+bb.length;
      if(!this.__largestConv||size>this.__largestConv.size)
        this.__largestConv={a,b,ctxDepth:ctx.length,size,leftBytes:ab.length,rightBytes:bb.length,step:this.steps};
    }
    throw e;
  }
};

for(const name of ["init-prelude","perf/grind-ring-5"]){
  const seen=[],capture=p.run;
  p.run=function(...xs){seen.push(this);return capture.apply(this,xs);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  let r;try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=run0;}
  let best=null;for(const k of seen)if(k.__largestConv&&(!best||k.__largestConv.size>best.size))best=k.__largestConv;
  const out={name,status:r.status,reason:r.reason,steps:r.steps??null,frontier:r.frontier_declaration??null};
  if(best){
    Object.assign(out,{capturedStep:best.step,ctxDepth:best.ctxDepth,leftBytes:best.leftBytes,rightBytes:best.rightBytes,
      leftHead:head(best.a),rightHead:head(best.b),leftCount:count(best.a),rightCount:count(best.b),
      commonIdentity:commonIdentity(best.a,best.b),firstDiff:firstDiff(best.a,best.b)});
    const d=out.firstDiff?.path??"";
    out.leftPrefix=JSON.stringify(best.a).slice(0,700);
    out.rightPrefix=JSON.stringify(best.b).slice(0,700);
  }
  console.log("GIANT_CONVERSION_PAIR "+JSON.stringify(out));
}
