// Diagnostic only: current frontier for the three remaining non-creative declines.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import * as K from "./kernel.mjs";

const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const TARGETS=["init-prelude","perf/grind-ring-5","perf/shared-subterm"];
const budgets=[1_000_000,4_000_000];

const proto=K.Kernel.prototype;
const methods=["validate","shift","substitute","lowerBound","whnf","same","normal",
  "proofType","equal","instantiateDeclaration","sortOf","infer","inferProjection"];
const originals=new Map();
for(const n of methods){
  if(typeof proto[n]!=="function")continue;
  const f=proto[n];originals.set(n,f);
  proto[n]=function(...args){
    this.__remainProfile??={stack:[],calls:{},ticks:{}};
    const p=this.__remainProfile;p.calls[n]=(p.calls[n]??0)+1;p.stack.push(n);
    try{return f.apply(this,args);}finally{p.stack.pop();}
  };
}
const oldTick=proto.tick;
proto.tick=function(...args){
  this.__remainProfile??={stack:[],calls:{},ticks:{}};
  const p=this.__remainProfile,n=p.stack.at(-1)??"<other>";
  p.ticks[n]=(p.ticks[n]??0)+1;
  return oldTick.apply(this,args);
};
const oldResult=proto.result;
proto.result=function(...args){
  const r=oldResult.apply(this,args);
  r.__remainProfile=this.__remainProfile??null;
  return r;
};

const results=[];
for(const name of TARGETS){
  const path=new URL("../_build/tests/"+name+".ndjson",import.meta.url);
  const input=readFileSync(path,"utf8");
  const attempts=[];
  for(const budget of budgets){
    const t=Date.now(),r=K.checkExport(input,CAPS,budget);
    const profile=r.__remainProfile;
    const top=profile?Object.entries(profile.ticks).sort((a,b)=>b[1]-a[1]).slice(0,10)
      .map(([op,ticks])=>({op,ticks,calls:profile.calls[op]??0,
        share:ticks/Math.max(1,r.steps??budget)})):[];
    attempts.push({budget,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,parse_records:r.parse_records??null,
      elapsed_ms:Date.now()-t,frontier_declaration:r.frontier_declaration??null,top});
    if(r.status!=="UNKNOWN")break;
    if(!["budget-exhausted","host-stack-limit"].includes(r.reason))break;
  }
  results.push({name,input_bytes:input.length,input_lines:input.split(/\r?\n/).filter(Boolean).length,attempts});
}
for(const [n,f] of originals)proto[n]=f;
proto.tick=oldTick;proto.result=oldResult;

const summary={diagnostic:"remaining-declines-current-frontier",budgets,results,
  claim_boundary:"Instrumentation and budget scaling only; no kernel semantics or verdict policy changed."};
const out=new URL("./evidence/remaining-declines-current-frontier.json",import.meta.url);
mkdirSync(dirname(out.pathname),{recursive:true});
writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("REMAINING_DECLINES_FRONTIER "+JSON.stringify(summary));
