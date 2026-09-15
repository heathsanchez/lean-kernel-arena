import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype;
const methods=["validate","shift","substitute","lowerBound","functionEtaContract","whnf","same","normal","proofType","equal","instantiateDeclaration","sortOf","infer","inferProjection","instantiateForalls","splitAllForalls","getApp","hasConst","isUnitLikeType","structureEtaMatches","make"];
const originals=new Map();
for(const name of methods){
 if(typeof p[name]!=="function")continue;
 const orig=p[name]; originals.set(name,orig);
 p[name]=function(...args){
   this.__prof??={stack:[],ticks:{},calls:{},maxDepth:{}};
   const q=this.__prof;q.calls[name]=(q.calls[name]??0)+1;q.stack.push(name);
   q.maxDepth[name]=Math.max(q.maxDepth[name]??0,q.stack.length);
   try{return orig.apply(this,args);}finally{q.stack.pop();}
 };
}
const oldTick=p.tick,oldResult=p.result,oldRun=p.run;const kernels=[];
p.tick=function(...args){this.__prof??={stack:[],ticks:{},calls:{},maxDepth:{}};const top=this.__prof.stack.at(-1)??"<none>";this.__prof.ticks[top]=(this.__prof.ticks[top]??0)+1;return oldTick.apply(this,args);};
p.run=function(...args){kernels.push(this);return oldRun.apply(this,args);};
p.result=function(...args){const r=oldResult.apply(this,args);r.__prof=this.__prof;return r;};
const r=K.checkExport(readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8"),CAPS,1_000_000);
const prof=kernels[0]?.__prof??r.__prof??{ticks:{},calls:{},maxDepth:{}};
const top=Object.keys(prof.ticks).map(op=>({op,ticks:prof.ticks[op],calls:prof.calls[op]??0,avg:prof.ticks[op]/Math.max(1,prof.calls[op]??1),maxDepth:prof.maxDepth[op]??0})).sort((a,b)=>b.ticks-a.ticks);
const out={experiment:"shared-subterm-hotspot-profile",result:{status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed,elapsed_ms:r.elapsed_ms},top};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/shared-subterm-hotspot-profile.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_SUBTERM_HOTSPOT_PROFILE "+JSON.stringify(out));
