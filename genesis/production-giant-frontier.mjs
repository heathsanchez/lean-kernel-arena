import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import {checkExport} from "./production.mjs";

// Diagnostic only: profile the exact production runtime that qualification uses
// after the retained WHNF re-entry repair. No semantic rule or verdict policy is
// changed. The goal is to identify the next earned contraction after host-stack
// recursion has been removed.
const TARGETS=["init-prelude","perf/grind-ring-5","perf/shared-subterm"];
const BUDGETS=[2_000_000,4_000_000,8_000_000];
const METHODS=["validate","shift","substitute","lowerBound","whnf","same","normal",
  "proofType","equal","instantiateDeclaration","sortOf","infer","inferProjection","getApp"];

const proto=Kernel.prototype, originals=new Map();
for(const name of METHODS){
  if(typeof proto[name]!=="function") continue;
  const f=proto[name]; originals.set(name,f);
  proto[name]=function(...args){
    this.__prodGiantProfile??={stack:[],calls:{},ticks:{}};
    const p=this.__prodGiantProfile;
    p.calls[name]=(p.calls[name]??0)+1;
    p.stack.push(name);
    try{return f.apply(this,args);}finally{p.stack.pop();}
  };
}
const tick0=proto.tick;
proto.tick=function(...args){
  this.__prodGiantProfile??={stack:[],calls:{},ticks:{}};
  const p=this.__prodGiantProfile,name=p.stack.at(-1)??"<other>";
  p.ticks[name]=(p.ticks[name]??0)+1;
  return tick0.apply(this,args);
};
const result0=proto.result;
proto.result=function(...args){
  const r=result0.apply(this,args);
  r.__prodGiantProfile=this.__prodGiantProfile??null;
  return r;
};

const results=[];
for(const name of TARGETS){
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const attempts=[];
  for(const budget of BUDGETS){
    const started=Date.now();
    const r=checkExport(input,{semanticBudget:budget,inputBytes:20_000_000,recordLimit:400_000});
    const profile=r.__prodGiantProfile;
    const top=profile?Object.entries(profile.ticks)
      .sort((a,b)=>b[1]-a[1]).slice(0,15)
      .map(([op,ticks])=>({op,ticks,calls:profile.calls[op]??0,
        share:ticks/Math.max(1,r.steps??budget)})):[];
    attempts.push({budget,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,elapsed_ms:Date.now()-started,
      frontier_declaration:r.frontier_declaration??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null,top});
    if(r.status!=="UNKNOWN") break;
    if(!["budget-exhausted","host-stack-limit"].includes(r.reason)) break;
  }
  results.push({name,input_bytes:input.length,attempts});
}

for(const [name,f] of originals) proto[name]=f;
proto.tick=tick0; proto.result=result0;
const summary={diagnostic:"production-giant-frontier-after-whnf-reentry",
  budgets:BUDGETS,results,
  claim_boundary:"Exact production runtime profiling only; no checking semantics changed."};
const out=new URL("./evidence/production-giant-frontier.json",import.meta.url);
mkdirSync(dirname(out.pathname),{recursive:true});
writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("PRODUCTION_GIANT_FRONTIER "+JSON.stringify(summary));
