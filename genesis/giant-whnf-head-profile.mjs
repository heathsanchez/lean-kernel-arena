import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function rawHead(e){
  let h=e,args=0;
  while(Array.isArray(h)&&h[0]==="app"){args++;h=h[1];}
  if(!Array.isArray(h)) return {tag:typeof h,args};
  if(h[0]==="const") return {tag:"const",name:h[1],args};
  return {tag:h[0],args};
}

const p=K.Kernel.prototype,whnf0=p.whnf,normal0=p.normal,run0=p.run;
p.run=function(...xs){
  this.__headProfile={whnf:new Map(),normal:new Map(),whnfDepth:0,normalDepth:0};
  return run0.apply(this,xs);
};
function bump(map,key,cost){
  let x=map.get(key);
  if(!x){x={calls:0,ticks:0,max:0};map.set(key,x);}
  x.calls++;x.ticks+=cost;if(cost>x.max)x.max=cost;
}
p.whnf=function(e){
  this.__headProfile??={whnf:new Map(),normal:new Map(),whnfDepth:0,normalDepth:0};
  const q=this.__headProfile,start=this.steps,h=rawHead(e),key=JSON.stringify(h);
  q.whnfDepth++;
  try{return whnf0.call(this,e);}
  finally{
    q.whnfDepth--;
    bump(q.whnf,key,Math.max(0,this.steps-start));
  }
};
p.normal=function(e){
  this.__headProfile??={whnf:new Map(),normal:new Map(),whnfDepth:0,normalDepth:0};
  const q=this.__headProfile,start=this.steps,h=rawHead(e),key=JSON.stringify(h);
  q.normalDepth++;
  try{return normal0.call(this,e);}
  finally{
    q.normalDepth--;
    bump(q.normal,key,Math.max(0,this.steps-start));
  }
};

const seen=[],oldRun=p.run;
p.run=function(...xs){seen.push(this);return oldRun.apply(this,xs);};
const input=readFileSync(new URL("../_build/tests/perf/grind-ring-5.ndjson",import.meta.url),"utf8");
const t0=Date.now();let r;
try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=oldRun;}
function merge(which){
  const m=new Map();
  for(const k of seen)for(const [key,x] of k.__headProfile?.[which]??[]){
    let y=m.get(key);if(!y){y={key,calls:0,ticks:0,max:0};m.set(key,y);}
    y.calls+=x.calls;y.ticks+=x.ticks;y.max=Math.max(y.max,x.max);
  }
  return [...m.values()].sort((a,b)=>b.ticks-a.ticks).slice(0,30);
}
console.log("GIANT_WHNF_HEAD_PROFILE "+JSON.stringify({
  status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
  frontier:r.frontier_declaration??null,elapsed_ms:Date.now()-t0,
  whnf:merge("whnf"),normal:merge("normal")
}));
