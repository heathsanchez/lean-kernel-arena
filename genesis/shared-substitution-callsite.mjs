import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype,stackMethods=["infer","whnf","instantiateForalls","instantiateDeclaration","equal","normal","sortOf","addSingleInductive","deriveTypeRecursor"];
for(const name of stackMethods){
  const orig=p[name];if(typeof orig!=="function")continue;
  p[name]=function(...args){
    this.__callerStack??=[];this.__callerStack.push(name);
    try{return orig.apply(this,args);}finally{this.__callerStack.pop();}
  };
}
const sub0=p.substitute,run0=p.run,seen=[];
p.run=function(...args){this.__callerStack=[];this.__subDepth=0;this.__subCaller=new Map();seen.push(this);return run0.apply(this,args);};
p.substitute=function(root,arg,depth=0){
  const outer=(this.__subDepth??0)===0;
  this.__subDepth=(this.__subDepth??0)+1;
  const caller=outer?(this.__callerStack?.at(-1)??"<none>"):null,before=this.steps??0;
  try{return sub0.call(this,root,arg,depth);}
  finally{
    this.__subDepth--;
    if(outer){
      const cost=(this.steps??0)-before,q=this.__subCaller.get(caller)??{caller,calls:0,totalCost:0,maxCost:0};
      q.calls++;q.totalCost+=cost;q.maxCost=Math.max(q.maxCost,cost);this.__subCaller.set(caller,q);
    }
  }
};
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const t0=Date.now(),r=K.checkExport(input,CAPS,1_000_000);
const callers=[];
for(const k of seen)for(const q of k.__subCaller?.values()??[])callers.push({...q,avgCost:q.totalCost/Math.max(1,q.calls)});
callers.sort((a,b)=>b.totalCost-a.totalCost);
const out={experiment:"shared-substitution-callsite",result:{status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0},callers};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/shared-substitution-callsite.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_SUBSTITUTION_CALLSITE "+JSON.stringify(out));
