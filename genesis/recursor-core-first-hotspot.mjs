import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");
await import("./compiled-dynamic-slot-layer.mjs");
await import("./recursor-core-first-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const p=K.Kernel.prototype,names=["validate","shift","substitute","same","whnf","normal","proofType","equal",
"instantiateDeclaration","sortOf","infer","getApp","appN","hasConst","lowerBound","functionEtaContract",
"isUnitLikeType","structureEtaMatches","inferProjection","instantiateForalls","splitAllForalls","deriveTypeRecursor","addSingleInductive"];
const originals=new Map();
for(const name of names){
 if(typeof p[name]!=="function")continue;
 const orig=p[name];originals.set(name,orig);
 p[name]=function(...args){
   this.__hot??={stack:[],ticks:{},calls:{},edges:{}};
   const parent=this.__hot.stack.at(-1)??"<root>";
   this.__hot.calls[name]=(this.__hot.calls[name]??0)+1;
   const edge=parent+"->"+name;this.__hot.edges[edge]=(this.__hot.edges[edge]??0)+1;
   this.__hot.stack.push(name);
   try{return orig.apply(this,args);}finally{this.__hot.stack.pop();}
 };
}
const tick0=p.tick;p.tick=function(...args){
 this.__hot??={stack:[],ticks:{},calls:{},edges:{}};
 const n=this.__hot.stack.at(-1)??"<root>";this.__hot.ticks[n]=(this.__hot.ticks[n]??0)+1;
 return tick0.apply(this,args);
};
const result0=p.result;p.result=function(...args){const r=result0.apply(this,args);r.__hot=this.__hot;return r;};
const r=K.checkExport(input,CAPS,1_000_000),h=r.__hot??{ticks:{},calls:{},edges:{}};
const hot=Object.entries(h.ticks).sort((a,b)=>b[1]-a[1]).map(([method,ticks])=>({method,ticks,share:ticks/Math.max(1,r.steps??1),calls:h.calls[method]??0}));
const edges=Object.entries(h.edges).sort((a,b)=>b[1]-a[1]).slice(0,30).map(([edge,calls])=>({edge,calls}));
console.log("CORE_FIRST_HOTSPOT "+JSON.stringify({status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,hot:hot.slice(0,15),edges,
 core:{...((r.__kernel?.__recCoreStats)??{})}}));
