import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype,sub0=p.substitute,run0=p.run,seen=[];

function oid(k,e){
  if(!Array.isArray(e))return "p:"+String(e);
  k.__substIds??=new WeakMap();k.__substNext??=1;
  let id=k.__substIds.get(e);if(id===undefined){id=k.__substNext++;k.__substIds.set(e,id);}return id;
}
p.run=function(...args){
  this.__substIds=new WeakMap();this.__substNext=1;this.__substDepth=0;this.__substRows=new Map();
  seen.push(this);return run0.apply(this,args);
};
p.substitute=function(root,arg,depth=0){
  const outer=(this.__substDepth??0)===0;
  this.__substDepth=(this.__substDepth??0)+1;
  const before=this.steps??0;
  try{return sub0.call(this,root,arg,depth);}
  finally{
    this.__substDepth--;
    if(outer){
      const cost=(this.steps??0)-before,key=oid(this,root)+":"+depth;
      const q=this.__substRows.get(key)??{rootId:oid(this,root),depth,calls:0,totalCost:0,maxCost:0,args:new Set(),rootTag:Array.isArray(root)?root[0]:typeof root};
      q.calls++;q.totalCost+=cost;q.maxCost=Math.max(q.maxCost,cost);q.args.add(oid(this,arg));this.__substRows.set(key,q);
    }
  }
};

const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const t0=Date.now(),r=K.checkExport(input,CAPS,1_000_000);
const rows=[];
for(const k of seen)for(const q of k.__substRows?.values()??[]){
  rows.push({rootId:q.rootId,depth:q.depth,rootTag:q.rootTag,calls:q.calls,totalCost:q.totalCost,maxCost:q.maxCost,
    avgCost:q.totalCost/Math.max(1,q.calls),distinctArgs:q.args.size});
}
rows.sort((a,b)=>b.totalCost-a.totalCost);
const out={experiment:"shared-head-beta-substitution-census",
 result:{status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0},
 top:rows.slice(0,40),totalTopLevelCalls:rows.reduce((n,q)=>n+q.calls,0),distinctPrograms:rows.length,
 prefixHits:seen.reduce((n,k)=>n+(k.__recPrefixHits??0),0),
 headBetaSpines:seen.reduce((n,k)=>n+(k.__headBetaSpines??0),0)};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/shared-head-beta-substitution-census.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_HEAD_BETA_SUBSTITUTION_CENSUS "+JSON.stringify(out));
