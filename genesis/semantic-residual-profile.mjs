import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

const p=K.Kernel.prototype;
const methods=["validate","shift","substitute","lowerBound","whnf","same","normal","proofType","equal",
"instantiateDeclaration","sortOf","infer","inferProjection","getApp","make","appN","splitAllForalls","instantiateForalls"];
for(const n of methods){
  if(typeof p[n]!=="function") continue;
  const f=p[n];
  p[n]=function(...args){
    this.__semProfile??={stack:[],calls:{},ticks:{},byDecl:{}};
    const q=this.__semProfile;
    q.calls[n]=(q.calls[n]??0)+1;
    q.stack.push(n);
    try{return f.apply(this,args);}
    finally{q.stack.pop();}
  };
}
const tick0=p.tick;
p.tick=function(...args){
  this.__semProfile??={stack:[],calls:{},ticks:{},byDecl:{}};
  const q=this.__semProfile,op=q.stack.at(-1)??"<other>";
  q.ticks[op]=(q.ticks[op]??0)+1;
  const d=this.currentDeclaration??"<none>";
  const m=q.byDecl[d]??=(Object.create(null));
  m[op]=(m[op]??0)+1;
  return tick0.apply(this,args);
};
const result0=p.result;
p.result=function(...args){
  const r=result0.apply(this,args);
  const q=this.__semProfile;
  if(q){
    const top=Object.entries(q.ticks).sort((a,b)=>b[1]-a[1]).slice(0,20)
      .map(([op,ticks])=>({op,ticks,calls:q.calls[op]??0,share:ticks/Math.max(1,r.steps??1)}));
    const d=this.currentDeclaration??"<none>",dt=q.byDecl[d]??{};
    const declTop=Object.entries(dt).sort((a,b)=>b[1]-a[1]).slice(0,20)
      .map(([op,ticks])=>({op,ticks}));
    r.__semProfile={top,declTop};
  }
  return r;
};

for(const name of ["init-prelude","perf/grind-ring-5"]){
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now(),r=K.checkExport(input,CAPS,2_000_000);
  console.log("SEMANTIC_RESIDUAL_PROFILE "+JSON.stringify({
    name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    frontier:r.frontier_declaration??null,top:r.__semProfile?.top??null,declTop:r.__semProfile?.declTop??null,
    elapsed_ms:Date.now()-t0
  }));
}
