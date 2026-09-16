import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import {checkExport} from "./production.mjs";
await import("./prefix-certified-current-layer.mjs");

const budget=Number(process.env.BUDGET??4_000_000);
const TARGETS=["init-prelude","perf/grind-ring-5","perf/shared-subterm"];
const p=Kernel.prototype;
const originals=new Map();
const excluded=new Set(["constructor","run","tick","result"]);
for(const name of Object.getOwnPropertyNames(p)){
  if(excluded.has(name)||typeof p[name]!=="function")continue;
  const f=p[name];originals.set(name,f);
  p[name]=function(...args){
    this.__prefixHotProfile??={stack:[],calls:{},ticks:{}};
    const q=this.__prefixHotProfile;q.calls[name]=(q.calls[name]??0)+1;q.stack.push(name);
    try{return f.apply(this,args);}finally{q.stack.pop();}
  };
}
const tick0=p.tick,run0=p.run;
p.tick=function(...args){
  this.__prefixHotProfile??={stack:[],calls:{},ticks:{}};
  const q=this.__prefixHotProfile,name=q.stack.at(-1)??"<other>";
  q.ticks[name]=(q.ticks[name]??0)+1;
  return tick0.apply(this,args);
};

const rows=[];
for(const name of TARGETS){
  const seen=[];
  p.run=function(...args){
    this.__prefixHotProfile={stack:[],calls:{},ticks:{}};seen.push(this);
    return run0.apply(this,args);
  };
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();
  const r=checkExport(input,{semanticBudget:budget,inputBytes:20_000_000,recordLimit:400_000});
  const kernels=seen.map((k,index)=>{
    const q=k.__prefixHotProfile??{calls:{},ticks:{}};
    const top=Object.entries(q.ticks).sort((a,b)=>b[1]-a[1]).slice(0,30)
      .map(([op,ticks])=>({op,ticks,calls:q.calls[op]??0,share:ticks/Math.max(1,k.steps??budget)}));
    return {index,localDefs:k.localDefs===true,steps:k.steps??null,constructed:k.allocations??null,
      prefixCertified:k.__prefixCertifiedStats??null,
      recPrefix:{hits:k.__recPrefixHits??0,stores:k.__recPrefixStores??0,reductions:k.__recPrefixReductions??0},top};
  });
  rows.push({name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    elapsed_ms:Date.now()-t0,frontier:r.frontier_declaration??null,
    fallback_attempt_reason:r.fallback_attempt_reason??null,fallback_attempt_steps:r.fallback_attempt_steps??null,kernels});
}
p.run=run0;p.tick=tick0;for(const [name,f] of originals)p[name]=f;
const out={experiment:"prefix-certified-hotspot-profile",budget,rows,
  claim_boundary:"Diagnostic attribution over the exact prefix-certified current-production separator. Method wrappers only attribute existing semantic ticks; they do not add checking rules or alter the requested semantic budget."};
const path=new URL(`./evidence/prefix-certified-hotspot-${budget}.json`,import.meta.url);
mkdirSync(dirname(path.pathname),{recursive:true});writeFileSync(path,JSON.stringify(out,null,2)+"\n");
console.log("PREFIX_CERTIFIED_HOTSPOT "+JSON.stringify(out));
