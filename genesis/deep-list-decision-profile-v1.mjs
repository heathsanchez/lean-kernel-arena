import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {resolve,dirname} from "node:path";
import * as P from "./production.mjs";
import "./deep-list-symbolic-nat-layer-v1.mjs";
import {Kernel,Stop} from "./kernel-base.mjs";
import {displayName} from "./name-codec.mjs";

const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGET=2_000_000;
const WATCH=new Set([
  "Decidable.decide",
  "Decidable.casesOn",
  "Nat.decLt",
  "Nat.decLe",
  "Nat.ble",
  "OfNat.ofNat",
  "UInt32.size",
]);
Error.stackTraceLimit=50;

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function headName(e){
  const {h}=spine(e);
  return Array.isArray(h)&&h[0]==="const"?displayName(h[1]):null;
}
function headSketch(e){
  if(!Array.isArray(e))return {tag:typeof e};
  const {h,args}=spine(e);
  return {
    tag:e[0],
    arity:args.length,
    name:Array.isArray(h)&&h[0]==="const"?displayName(h[1]):null,
    headTag:Array.isArray(h)?h[0]:typeof h,
  };
}
function inTarget(k){
  return displayName(k.currentDeclaration).endsWith("isValidChar_UInt32");
}
function keepTop(rows,row,limit=12){
  rows.push(row);rows.sort((a,b)=>b.cost-a.cost);rows.length=Math.min(limit,rows.length);
}
function mkState(){
  return Object.fromEntries([...WATCH].map(name=>[name,{calls:0,steps:0,max:0,top:[],ok:0,stop:0}]));
}

const whnf0=Kernel.prototype.whnf;
const run0=Kernel.prototype.run;
const states=new WeakMap();
function state(k){let s=states.get(k);if(!s){s=mkState();states.set(k,s);}return s;}

Kernel.prototype.run=function(...args){state(this);return run0.apply(this,args);};
Kernel.prototype.whnf=function(e){
  if(!inTarget(this))return whnf0.call(this,e);
  const name=headName(e);
  if(!WATCH.has(name))return whnf0.call(this,e);
  const bucket=state(this)[name],start=this.steps;
  bucket.calls++;
  try{
    const out=whnf0.call(this,e);
    const cost=this.steps-start;
    bucket.steps+=cost;bucket.max=Math.max(bucket.max,cost);bucket.ok++;
    if(cost>=250)keepTop(bucket.top,{
      cost,result:"ok",step:start,input:headSketch(e),output:headSketch(out),
      inputPrefix:JSON.stringify(e).slice(0,3500),
      outputPrefix:JSON.stringify(out).slice(0,1800),
    });
    return out;
  }catch(err){
    const cost=Math.max(0,this.steps-start);
    bucket.steps+=cost;bucket.max=Math.max(bucket.max,cost);bucket.stop++;
    if(cost>=250)keepTop(bucket.top,{
      cost,result:err?.message??String(err),step:start,input:headSketch(e),
      inputPrefix:JSON.stringify(e).slice(0,3500),
      stack:String(err?.stack??"").split("\n").slice(0,45),
    });
    throw err;
  }
};

const rows=[];
for(const name of TARGETS){
  const seen=[];
  const capture0=Kernel.prototype.run;
  Kernel.prototype.run=function(...args){seen.push(this);return capture0.apply(this,args);};
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const t0=Date.now();let result;
  try{
    result=P.checkExport(input,{
      semanticBudget:BUDGET,
      inputBytes:20_000_000,
      recordLimit:400_000,
    });
  }finally{
    Kernel.prototype.run=capture0;
  }
  const merged=mkState();
  for(const k of seen){
    const s=state(k);
    for(const key of WATCH){
      const a=merged[key],b=s[key];
      a.calls+=b.calls;a.steps+=b.steps;a.max=Math.max(a.max,b.max);
      a.ok+=b.ok;a.stop+=b.stop;
      for(const x of b.top)keepTop(a.top,x);
    }
  }
  const row={
    name,
    result:{status:result.status,reason:result.reason??null,steps:result.steps??null,frontier:result.frontier_declaration??null},
    watched:merged,
    elapsed_ms:Date.now()-t0,
  };
  rows.push(row);
  console.log("DEEP_LIST_DECISION_PROFILE "+JSON.stringify({
    name,
    result:row.result,
    watched:Object.fromEntries([...WATCH].map(key=>[key,{
      calls:merged[key].calls,steps:merged[key].steps,max:merged[key].max,
      ok:merged[key].ok,stop:merged[key].stop,top:merged[key].top.slice(0,4),
    }])),
  }));
}
Kernel.prototype.whnf=whnf0;Kernel.prototype.run=run0;

const report={
  schema:"deep-list-decision-profile-v1",
  claim_boundary:"Diagnostic only. Profiles existing WHNF execution inside the exact isValidChar_UInt32 frontier; no checking semantics are changed.",
  budget:BUDGET,
  rows,
  gates:{
    both_frontier_is_isvalidchar:rows.every(r=>String(r.result.frontier).includes("isValidChar_UInt32")),
    decidable_decide_observed:rows.every(r=>r.watched["Decidable.decide"].calls>0),
    nat_decl_path_observed:rows.every(r=>
      r.watched["Nat.decLt"].calls+r.watched["Nat.decLe"].calls+r.watched["Nat.ble"].calls>0
    ),
  },
};
mkdirSync(dirname("genesis/evidence/deep-list-decision-profile-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/deep-list-decision-profile-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("DEEP_LIST_DECISION_PROFILE_RESULT="+JSON.stringify({
  gates:report.gates,
  rows:rows.map(r=>({name:r.name,result:r.result,watched:Object.fromEntries(
    [...WATCH].map(key=>[key,{calls:r.watched[key].calls,steps:r.watched[key].steps,max:r.watched[key].max,top:r.watched[key].top.slice(0,2)}])
  )})),
}));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_DEEP_LIST_DECISION_PROFILE_V1");
