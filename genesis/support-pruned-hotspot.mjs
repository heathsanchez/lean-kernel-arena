import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");
await import("./compiled-dynamic-slot-layer.mjs");
await import("./support-pruned-substitution-layer.mjs");
await import("./recursor-core-first-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const p=K.Kernel.prototype,names=["make","validate","shift","substitute","same","whnf","normal","proofType","equal",
"instantiateDeclaration","sortOf","infer","getApp","appN","hasConst","lowerBound","functionEtaContract",
"isUnitLikeType","structureEtaMatches","inferProjection","instantiateForalls","splitAllForalls","deriveTypeRecursor","addSingleInductive"];
const origs=new Map();
for(const n of names){
 if(typeof p[n]!=="function")continue;
 const f=p[n];origs.set(n,f);p[n]=function(...args){
  this.__sph??={stack:[],ticks:{},calls:{},edges:{}};
  const par=this.__sph.stack.at(-1)??"<root>";this.__sph.calls[n]=(this.__sph.calls[n]??0)+1;
  const edge=par+"->"+n;this.__sph.edges[edge]=(this.__sph.edges[edge]??0)+1;
  this.__sph.stack.push(n);try{return f.apply(this,args);}finally{this.__sph.stack.pop();}
 };
}
const tick0=p.tick;p.tick=function(...a){this.__sph??={stack:[],ticks:{},calls:{},edges:{}};
 const n=this.__sph.stack.at(-1)??"<root>";this.__sph.ticks[n]=(this.__sph.ticks[n]??0)+1;return tick0.apply(this,a);};
const res0=p.result;p.result=function(...a){const r=res0.apply(this,a);r.__sph=this.__sph;return r;};
const r=K.checkExport(input,CAPS,1_000_000),h=r.__sph??{ticks:{},calls:{},edges:{}};
const hot=Object.entries(h.ticks).sort((a,b)=>b[1]-a[1]).map(([method,ticks])=>({method,ticks,calls:h.calls[method]??0}));
const edges=Object.entries(h.edges).sort((a,b)=>b[1]-a[1]).slice(0,30).map(([edge,calls])=>({edge,calls}));
console.log("SUPPORT_PRUNED_HOTSPOT "+JSON.stringify({status:r.status,reason:r.reason,steps:r.steps??null,
 constructed:r.constructed??null,hot:hot.slice(0,15),edges}));
