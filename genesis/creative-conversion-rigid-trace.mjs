// Diagnostic only: localize the exact equality stack that produces
// rigid-head-mismatch on the two creative-conversion ACCEPT witnesses.
// This wrapper changes no equality outcome and performs no speculative proof.
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
const BUDGET=1_000_000;
const TARGETS=[
  "undecidability/alg-conv-trans-acc-left",
  "undecidability/subject-reduction-redex"
];

function nameLabel(n){
  if(typeof n!=="string") return String(n);
  let cur=n,parts=[];
  for(let i=0;i<24;i++){
    let x;
    try{x=JSON.parse(cur);}catch{return parts.length?parts.reverse().join("."):n;}
    if(!Array.isArray(x)||x.length!==3||(x[1]!=="str"&&x[1]!=="num"))
      return parts.length?parts.reverse().join("."):n;
    parts.push(String(x[2]));cur=x[0];
    if(cur==="[]") return parts.reverse().join(".");
  }
  return parts.reverse().join(".");
}
function rawSpine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse();return {head:e,args};
}
function atom(e){
  if(!Array.isArray(e)) return {tag:typeof e,value:String(e)};
  if(e[0]==="const") return {tag:"const",name:nameLabel(e[1]),levels:(e[2]??[]).length};
  if(e[0]==="var") return {tag:"var",index:e[1]};
  if(e[0]==="sort") return {tag:"sort",level:typeof e[1]==="number"?e[1]:"symbolic"};
  if(e[0]==="nat"||e[0]==="strlit") return {tag:e[0],value:e[1]};
  return {tag:e[0]};
}
function termSummary(e){
  if(!Array.isArray(e)) return atom(e);
  const s=rawSpine(e);
  if(s.args.length) return {
    tag:"app",head:atom(s.head),arity:s.args.length,
    argTags:s.args.slice(0,12).map(x=>Array.isArray(x)?x[0]:typeof x)
  };
  if(e[0]==="pi"||e[0]==="lam") return {tag:e[0],domain:atom(e[1]),body:atom(e[2])};
  if(e[0]==="proj") return {tag:"proj",type:nameLabel(e[1]),index:e[2],struct:atom(e[3])};
  return atom(e);
}
function sameRawHead(k,a,b){
  const x=rawSpine(a),y=rawSpine(b);
  return x.args.length>0&&x.args.length===y.args.length&&
    (x.head===y.head||(Array.isArray(x.head)&&Array.isArray(y.head)&&k.same(x.head,y.head)));
}

const proto=K.Kernel.prototype;
const retained=proto.equal;
const traceByKernel=new WeakMap();

function state(k){
  let s=traceByKernel.get(k);
  if(!s){
    s={calls:0,maxDepth:0,sameRawHeadCalls:0,rigidFrames:[],eligibleSamples:[]};
    traceByKernel.set(k,s);
  }
  return s;
}

proto.equal=function(a,b,ctx=[]){
  const st=state(this);
  const depth=(this.__creativeTraceDepth??0);
  this.__creativeTraceDepth=depth+1;
  st.calls++;st.maxDepth=Math.max(st.maxDepth,depth);
  const sameHead=sameRawHead(this,a,b);
  if(sameHead){
    st.sameRawHeadCalls++;
    if(st.eligibleSamples.length<40) st.eligibleSamples.push({
      depth,decl:nameLabel(this.currentDeclaration),ctx:ctx.length,steps:this.steps,
      a:termSummary(a),b:termSummary(b)
    });
  }
  try{
    return retained.call(this,a,b,ctx);
  }catch(e){
    if(e instanceof K.Stop && e.status===K.REJECT && e.message==="rigid-head-mismatch"){
      // Every propagating equal frame is useful: together these reconstruct
      // the exact conversion path from the declaration obligation to the
      // deepest rigid mismatch.
      if(st.rigidFrames.length<160) st.rigidFrames.push({
        depth,decl:nameLabel(this.currentDeclaration),ctx:ctx.length,steps:this.steps,
        sameRawHead:sameHead,a:termSummary(a),b:termSummary(b)
      });
    }
    throw e;
  }finally{
    this.__creativeTraceDepth=depth;
  }
};

function inputFor(name){
  return readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
}

const rows=[];
for(const name of TARGETS){
  // checkExport can construct more than one Kernel only for UNKNOWN fallbacks.
  // These witnesses reject in the retained kernel, so the state associated with
  // the rejecting kernel is the final trace. Gather all kernel states by
  // instrumenting run just for this invocation.
  const seen=[];
  const retainedRun=proto.run;
  proto.run=function(...args){
    seen.push(this);
    return retainedRun.apply(this,args);
  };
  const result=K.checkExport(inputFor(name),CAPS,BUDGET);
  proto.run=retainedRun;
  rows.push({
    name,result,
    kernels:seen.map(k=>state(k)).map(s=>({
      ...s,
      // Throw propagation records deepest frame first; preserve that order.
      rigidFrames:s.rigidFrames,
      eligibleSamples:s.eligibleSamples
    }))
  });
}
proto.equal=retained;

const summary={
  diagnostic:"creative-conversion-rigid-mismatch-trace",
  budget:BUDGET,rows,
  claim_boundary:"Diagnostic wrapper only. Equality, reduction, proof irrelevance, budgets, and verdicts are unchanged; it records raw equality call shapes and the propagating rigid-head-mismatch stack."
};
const out=new URL("./evidence/creative-conversion-rigid-trace.json",import.meta.url);
mkdirSync(dirname(out.pathname),{recursive:true});
writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
for(const row of rows){
  const k=row.kernels[0]??{};
  console.log("CREATIVE_RIGID_TRACE "+JSON.stringify({
    name:row.name,result:row.result,calls:k.calls,maxDepth:k.maxDepth,
    sameRawHeadCalls:k.sameRawHeadCalls,
    rigidFrames:(k.rigidFrames??[]).slice(0,30),
    eligibleSamples:(k.eligibleSamples??[]).slice(-12)
  }));
}
