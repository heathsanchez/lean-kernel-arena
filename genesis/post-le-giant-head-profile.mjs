import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";
import "./compiled-le-nat-dictionary-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function rawHead(e){
 let h=e,args=0;while(Array.isArray(h)&&h[0]==="app"){args++;h=h[1];}
 if(!Array.isArray(h))return{tag:typeof h,args};
 return h[0]==="const"?{tag:"const",name:h[1],args}:{tag:h[0],args};
}
const p=K.Kernel.prototype;
for(const n of ["whnf","normal"]){
 const f=p[n];
 p[n]=function(e,...rest){
  this.__postLEProfile??={whnf:new Map(),normal:new Map()};
  const m=this.__postLEProfile[n],key=JSON.stringify(rawHead(e)),start=this.steps;
  try{return f.call(this,e,...rest);}finally{
   const cost=Math.max(0,this.steps-start);let x=m.get(key);
   if(!x){x={calls:0,ticks:0,max:0};m.set(key,x);}
   x.calls++;x.ticks+=cost;x.max=Math.max(x.max,cost);
  }
 };
}
const input=readFileSync(new URL("../_build/tests/perf/grind-ring-5.ndjson",import.meta.url),"utf8");
const seen=[],run0=p.run;p.run=function(...xs){seen.push(this);return run0.apply(this,xs);};
const t0=Date.now();let r;try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=run0;}
function merge(kind){
 const m=new Map();for(const k of seen)for(const [key,x] of k.__postLEProfile?.[kind]??[]){
  let y=m.get(key);if(!y){y={key,calls:0,ticks:0,max:0};m.set(key,y);}
  y.calls+=x.calls;y.ticks+=x.ticks;y.max=Math.max(y.max,x.max);
 }
 return [...m.values()].sort((a,b)=>b.ticks-a.ticks).slice(0,30);
}
console.log("POST_LE_HEAD_PROFILE "+JSON.stringify({
 status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
 frontier:r.frontier_declaration??null,leNatHits:seen.reduce((n,k)=>n+(k.__compiledLENatHits??0),0),
 whnf:merge("whnf"),normal:merge("normal"),elapsed_ms:Date.now()-t0
}));
