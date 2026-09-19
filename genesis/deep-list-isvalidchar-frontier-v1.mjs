import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname,resolve} from "node:path";
import * as P from "./production.mjs";
import "./deep-list-symbolic-nat-layer-v1.mjs";
import {Kernel,Stop} from "./kernel-base.mjs";
import {displayName} from "./name-codec.mjs";

const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGET=2_000_000;
const SLOW=2_000;
Error.stackTraceLimit=60;

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function head(e){
  if(!Array.isArray(e))return {tag:typeof e};
  const {h,args}=spine(e);
  const out={tag:e[0],arity:args.length};
  if(Array.isArray(h)&&h[0]==="const")out.name=displayName(h[1]);
  if(Array.isArray(h)&&h[0]==="var")out.var=h[1];
  return out;
}
function short(e){
  const raw=JSON.stringify(e);
  return {bytes:raw.length,head:head(e),prefix:raw.slice(0,5000)};
}
function inTarget(k){
  const n=displayName(k.currentDeclaration);
  return n.endsWith("isValidChar_UInt32");
}
function keepTop(rows,row,limit=30){
  rows.push(row);rows.sort((a,b)=>b.cost-a.cost);rows.length=Math.min(limit,rows.length);
}

const eq0=Kernel.prototype.equal;
const whnf0=Kernel.prototype.whnf;
const run0=Kernel.prototype.run;
const states=new WeakMap();
function state(k){
  let s=states.get(k);
  if(!s){s={equal_calls:0,equal_steps:0,whnf_calls:0,whnf_steps:0,slow_equal:[],slow_whnf:[],rejects:[]};states.set(k,s);}
  return s;
}

Kernel.prototype.run=function(...args){
  state(this);
  return run0.apply(this,args);
};
Kernel.prototype.equal=function(a,b,ctx=[]){
  if(!inTarget(this))return eq0.call(this,a,b,ctx);
  const s=state(this),start=this.steps;s.equal_calls++;
  try{
    const out=eq0.call(this,a,b,ctx);
    const cost=this.steps-start;s.equal_steps+=cost;
    if(cost>=SLOW)keepTop(s.slow_equal,{cost,result:"ok",step:start,ctx_depth:ctx.length,left:short(a),right:short(b)});
    return out;
  }catch(e){
    const cost=this.steps-start;s.equal_steps+=Math.max(0,cost);
    if(cost>=SLOW)keepTop(s.slow_equal,{cost,result:e?.message??String(e),step:start,ctx_depth:ctx.length,left:short(a),right:short(b),
      stack:String(e?.stack??"").split("\n").slice(0,60)});
    if(e instanceof Stop){
      s.rejects.push({status:e.status,reason:e.message,step:this.steps,left:short(a),right:short(b)});
      s.rejects=s.rejects.slice(-20);
    }
    throw e;
  }
};
Kernel.prototype.whnf=function(e){
  if(!inTarget(this))return whnf0.call(this,e);
  const s=state(this),start=this.steps;s.whnf_calls++;
  try{
    const out=whnf0.call(this,e),cost=this.steps-start;s.whnf_steps+=cost;
    if(cost>=SLOW)keepTop(s.slow_whnf,{cost,result:"ok",step:start,input:short(e),output:short(out)});
    return out;
  }catch(err){
    const cost=this.steps-start;s.whnf_steps+=Math.max(0,cost);
    if(cost>=SLOW)keepTop(s.slow_whnf,{cost,result:err?.message??String(err),step:start,input:short(e),
      stack:String(err?.stack??"").split("\n").slice(0,40)});
    throw err;
  }
};

const rows=[];
for(const name of TARGETS){
  const seen=[];
  const capture0=Kernel.prototype.run;
  Kernel.prototype.run=function(...args){seen.push(this);return capture0.apply(this,args);};
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  let result;
  try{
    result=P.checkExport(input,{
      semanticBudget:BUDGET,
      inputBytes:20_000_000,
      recordLimit:400_000,
    });
  }finally{
    Kernel.prototype.run=capture0;
  }
  const merged={equal_calls:0,equal_steps:0,whnf_calls:0,whnf_steps:0,slow_equal:[],slow_whnf:[],rejects:[],symbolic_nat_bool_hits:0};
  for(const k of seen){
    const s=state(k);
    merged.equal_calls+=s.equal_calls;merged.equal_steps+=s.equal_steps;
    merged.whnf_calls+=s.whnf_calls;merged.whnf_steps+=s.whnf_steps;
    merged.symbolic_nat_bool_hits+=(k.__symbolicNatBoolHits??0);
    for(const x of s.slow_equal)keepTop(merged.slow_equal,x);
    for(const x of s.slow_whnf)keepTop(merged.slow_whnf,x);
    merged.rejects.push(...s.rejects);
  }
  merged.rejects=merged.rejects.slice(-30);
  const row={
    name,
    result:{status:result.status,reason:result.reason??null,steps:result.steps??null,frontier:result.frontier_declaration??null},
    profile:merged,
  };
  rows.push(row);
  console.log("DEEP_LIST_ISVALIDCHAR_FRONTIER "+JSON.stringify({
    name,
    result:row.result,
    symbolicHits:merged.symbolic_nat_bool_hits,
    equalCalls:merged.equal_calls,
    equalSteps:merged.equal_steps,
    whnfCalls:merged.whnf_calls,
    whnfSteps:merged.whnf_steps,
    topEqual:merged.slow_equal.slice(0,8),
    topWhnf:merged.slow_whnf.slice(0,8),
    rejects:merged.rejects.slice(-8),
  }));
}
Kernel.prototype.equal=eq0;Kernel.prototype.whnf=whnf0;Kernel.prototype.run=run0;

const report={
  schema:"deep-list-isvalidchar-frontier-v1",
  claim_boundary:"Diagnostic only. Reuses the bounded symbolic Nat repair candidate solely to expose the next exact cost frontier inside isValidChar_UInt32; no production semantics are promoted.",
  budget:BUDGET,
  rows,
  gates:{
    both_remain_nonreject:rows.every(r=>r.result.status!=="REJECT"),
    both_frontier_is_isvalidchar:rows.every(r=>String(r.result.frontier).includes("isValidChar_UInt32")),
    symbolic_nat_repair_is_active:rows.every(r=>r.profile.symbolic_nat_bool_hits>0),
    captures_expensive_isvalidchar_work:rows.every(r=>r.profile.slow_equal.length+r.profile.slow_whnf.length>0),
  },
};
mkdirSync(dirname("genesis/evidence/deep-list-isvalidchar-frontier-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/deep-list-isvalidchar-frontier-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("DEEP_LIST_ISVALIDCHAR_FRONTIER_RESULT="+JSON.stringify({
  gates:report.gates,
  rows:rows.map(r=>({name:r.name,result:r.result,topEqual:r.profile.slow_equal.slice(0,3),topWhnf:r.profile.slow_whnf.slice(0,3)})),
}));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_DEEP_LIST_ISVALIDCHAR_FRONTIER_V1");
