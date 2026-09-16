import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

const p=K.Kernel.prototype;
const methods=["shift","substitute","whnf","normal","equal","infer","sortOf","same","make","instantiateDeclaration","getApp","appN"];
const originals=new Map();
for(const name of methods){
 const orig=p[name];if(typeof orig!=="function")continue;
 originals.set(name,orig);
 p[name]=function(...args){
   this.__prof??={stack:[],ticks:{},calls:{},maxDepth:{}};
   const q=this.__prof;q.calls[name]=(q.calls[name]??0)+1;q.stack.push(name);
   q.maxDepth[name]=Math.max(q.maxDepth[name]??0,q.stack.length);
   try{return orig.apply(this,args);}finally{q.stack.pop();}
 };
}
const tick0=p.tick,run0=p.run;
p.tick=function(...args){
 this.__prof??={stack:[],ticks:{},calls:{},maxDepth:{}};
 const top=this.__prof.stack.at(-1)??"<none>";
 this.__prof.ticks[top]=(this.__prof.ticks[top]??0)+1;
 return tick0.apply(this,args);
};
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const runs=[];
for(const budget of [1_000_000,2_000_000,4_000_000,8_000_000]){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;
 try{r=K.checkExport(input,CAPS,budget);}finally{p.run=old;}
 const merged={ticks:{},calls:{},maxDepth:{}};
 for(const k of seen){
   const q=k.__prof??{ticks:{},calls:{},maxDepth:{}};
   for(const [n,v] of Object.entries(q.ticks))merged.ticks[n]=(merged.ticks[n]??0)+v;
   for(const [n,v] of Object.entries(q.calls))merged.calls[n]=(merged.calls[n]??0)+v;
   for(const [n,v] of Object.entries(q.maxDepth))merged.maxDepth[n]=Math.max(merged.maxDepth[n]??0,v);
 }
 const top=Object.keys(merged.ticks).map(op=>({op,ticks:merged.ticks[op],calls:merged.calls[op]??0,
   avg:merged.ticks[op]/Math.max(1,merged.calls[op]??1),maxDepth:merged.maxDepth[op]??0}))
   .sort((a,b)=>b.ticks-a.ticks);
 const row={budget,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
   elapsed_ms:Date.now()-t0,frontier_declaration:r.frontier_declaration??null,top};
 runs.push(row);console.log("RUN "+JSON.stringify(row));
 if(r.status==="ACCEPT")break;
}
const out={experiment:"shared-subterm-current-completion-profile",runs};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/shared-subterm-current-completion-profile.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("SHARED_SUBTERM_CURRENT_COMPLETION "+JSON.stringify(out));
