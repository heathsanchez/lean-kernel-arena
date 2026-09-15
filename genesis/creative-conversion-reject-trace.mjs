// Diagnostic only: preserve the exact conversion stack and normalized pair
// responsible for rigid-head-mismatch on the two creative conversion witnesses.
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
const TARGETS=[
  "undecidability/alg-conv-trans-acc-left",
  "undecidability/subject-reduction-redex"
];

const p=K.Kernel.prototype;
const oldEqual=p.equal,oldNormal=p.normal,oldReject=p.reject,oldResult=p.result;

function short(e){
  if(!Array.isArray(e)) return {scalar:String(e)};
  let h=e,args=0;
  while(Array.isArray(h)&&h[0]==="app"){args++;h=h[1];}
  let bytes=null,json="";
  try{json=JSON.stringify(e);bytes=json.length;}catch{}
  return {
    tag:e[0],
    head_tag:Array.isArray(h)?h[0]:typeof h,
    head_name:Array.isArray(h)&&h[0]==="const"?h[1]:null,
    app_args:args,
    bytes,
    sample:json.slice(0,1600)
  };
}

p.equal=function(a,b,ctx=[]){
  this.__creativeEqStack??=[];
  const frame={
    depth:this.__creativeEqStack.length,
    ctx_depth:ctx?.length??0,
    steps_enter:this.steps??null,
    left:short(a),right:short(b),
    normals:[]
  };
  this.__creativeEqStack.push(frame);
  try{return oldEqual.call(this,a,b,ctx);}
  finally{this.__creativeEqStack.pop();}
};

p.normal=function(e){
  const out=oldNormal.call(this,e);
  const st=this.__creativeEqStack;
  if(st?.length){
    const f=st[st.length-1];
    if(f.normals.length<4) f.normals.push({input:short(e),output:short(out)});
  }
  return out;
};

p.reject=function(reason){
  if(reason==="rigid-head-mismatch" && !this.__creativeRejectTrace){
    this.__creativeRejectTrace={
      reason,
      declaration:this.currentDeclaration??null,
      steps:this.steps??null,
      stack:(this.__creativeEqStack??[]).map(f=>structuredClone(f))
    };
  }
  return oldReject.call(this,reason);
};

p.result=function(status,reason,start){
  const r=oldResult.call(this,status,reason,start);
  if(this.__creativeRejectTrace) r.creative_reject_trace=this.__creativeRejectTrace;
  return r;
};

const rows=[];
for(const name of TARGETS){
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const r=K.checkExport(input,CAPS,1_000_000);
  rows.push({name,result:r});
}
p.equal=oldEqual;p.normal=oldNormal;p.reject=oldReject;p.result=oldResult;

const out={rows};
const path=new URL("./evidence/creative-conversion-reject-trace.json",import.meta.url);
mkdirSync(dirname(path.pathname),{recursive:true});
writeFileSync(path,JSON.stringify(out,null,2)+"\n");
console.log("CREATIVE_CONVERSION_TRACE "+JSON.stringify(out));
