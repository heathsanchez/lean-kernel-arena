import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype;
const methods=["shift","substitute","whnf","same","normal","equal","instantiateDeclaration","infer","getApp","make","appN"];
const originals=new Map();
for(const name of methods){
  const orig=p[name];if(typeof orig!=="function")continue;
  originals.set(name,orig);
  p[name]=function(...args){
    this.__postPrefixProf??={stack:[],ticks:{},calls:{}};
    const q=this.__postPrefixProf;
    q.calls[name]=(q.calls[name]??0)+1;
    q.stack.push(name);
    try{return orig.apply(this,args);}finally{q.stack.pop();}
  };
}
const tick0=p.tick,run0=p.run,seen=[];
p.tick=function(...args){
  this.__postPrefixProf??={stack:[],ticks:{},calls:{}};
  const q=this.__postPrefixProf,top=q.stack.at(-1)??"<none>";
  q.ticks[top]=(q.ticks[top]??0)+1;
  return tick0.apply(this,args);
};
p.run=function(...args){seen.push(this);return run0.apply(this,args);};

const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const t0=Date.now();
const result=K.checkExport(input,CAPS,1_000_000);
const merged={ticks:{},calls:{}};
for(const k of seen){
  const q=k.__postPrefixProf??{ticks:{},calls:{}};
  for(const [n,v] of Object.entries(q.ticks))merged.ticks[n]=(merged.ticks[n]??0)+v;
  for(const [n,v] of Object.entries(q.calls))merged.calls[n]=(merged.calls[n]??0)+v;
}
const top=Object.keys(merged.ticks).map(op=>({
  op,ticks:merged.ticks[op],calls:merged.calls[op]??0,
  avg:merged.ticks[op]/Math.max(1,merged.calls[op]??1)
})).sort((a,b)=>b.ticks-a.ticks);
const out={
  experiment:"shared-subterm-post-prefix-hotspot",
  result:{status:result.status,reason:result.reason,steps:result.steps??null,constructed:result.constructed??null,elapsed_ms:Date.now()-t0},
  prefixHits:seen.reduce((n,k)=>n+(k.__recPrefixHits??0),0),
  prefixStores:seen.reduce((n,k)=>n+(k.__recPrefixStores??0),0),
  prefixReductions:seen.reduce((n,k)=>n+(k.__recPrefixReductions??0),0),
  top
};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/shared-subterm-post-prefix-hotspot.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_SUBTERM_POST_PREFIX_HOTSPOT "+JSON.stringify(out));
