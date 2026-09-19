import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {Kernel,Stop,REJECT} from "./kernel-base.mjs";
import {leanName} from "./name-codec.mjs";
import * as P from "./production.mjs";

const N=leanName;
const ZERO=N("Nat","zero"),SUCC=N("Nat","succ");
const BLE=N("Nat","ble"),BEQ=N("Nat","beq");
const LAND=N("Nat","land"),SHIFTR=N("Nat","shiftRight");
const OFNAT=N("OfNat","ofNat"),INST_OF_NAT=N("instOfNatNat");
const NAT=N("Nat"),BTRUE=N("Bool","true"),BFALSE=N("Bool","false");
const PROFILE_DECL='["$lean-name-v1",["str","_private"],["str","Init"],["str","Prelude"],["num",0],["str","isValidChar_UInt32"]]';
const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGETS=[4_000_000];

const retainedWhnf=Kernel.prototype.whnf;
const retainedEqual=Kernel.prototype.equal;
const retainedRun=Kernel.prototype.run;
const retainedTick=Kernel.prototype.tick;
Error.stackTraceLimit=80;

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function natCtor(e){
  if(!Array.isArray(e)) return null;
  if(e[0]==="nat"){
    try{
      const n=BigInt(e[1]);
      if(n===0n)return {kind:"zero"};
      const p=n-1n;
      return {kind:"succ",pred:["nat",p<=BigInt(Number.MAX_SAFE_INTEGER)?Number(p):p.toString()]};
    }catch{return null;}
  }
  if(e[0]==="const"&&e[1]===ZERO&&(e[2]??[]).length===0)
    return {kind:"zero"};
  const s=spine(e);
  if(s.h?.[0]==="const"&&s.h[1]===SUCC&&(s.h[2]??[]).length===0&&s.args.length===1)
    return {kind:"succ",pred:s.args[0]};
  return null;
}
function bool(name){return ["const",name];}
function app2(k,h,a,b){return k.make("app",k.make("app",h,a),b);}
function natVal(e){
  if(!Array.isArray(e))return null;
  if(e[0]==="nat"){try{return BigInt(e[1]);}catch{return null;}}
  if(e[0]==="const"&&e[1]===ZERO&&(e[2]??[]).length===0)return 0n;
  const c=natCtor(e);
  if(c?.kind==="succ"){
    const p=natVal(c.pred); return p===null?null:p+1n;
  }
  return null;
}
function natExpr(v){
  return ["nat",v<=BigInt(Number.MAX_SAFE_INTEGER)?Number(v):v.toString()];
}
function exactNatOfNat(e){
  const {h,args}=spine(e);
  if(h?.[0]!=="const"||h[1]!==OFNAT||args.length!==3)return null;
  if(!(args[0]?.[0]==="const"&&args[0][1]===NAT))return null;
  const inst=spine(args[2]);
  if(!(inst.h?.[0]==="const"&&inst.h[1]===INST_OF_NAT&&inst.args.length===1))return null;
  const numeral=natVal(args[1]),witness=natVal(inst.args[0]);
  if(numeral===null||witness===null||numeral!==witness)return null;
  return natExpr(numeral);
}

Kernel.prototype.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const ofNat=exactNatOfNat(e);
    if(ofNat!==null){
      this.tick();this.need("reduction");this.need("declarations");
      this.__symbolicNatBoolHits=(this.__symbolicNatBoolHits??0)+1;
      return ofNat;
    }
    const {h,args}=spine(e);
    if(h?.[0]==="const"&&(h[2]??[]).length===0&&args.length===2&&
       (h[1]===LAND||h[1]===SHIFTR)){
      const wa=this.whnf(args[0]),wb=this.whnf(args[1]);
      const a=natVal(wa)??natVal(args[0]),b=natVal(wb)??natVal(args[1]);
      if(a!==null&&b!==null&&a>=0n&&b>=0n){
        this.tick();this.need("reduction");this.need("declarations");
        this.__symbolicNatBoolHits=(this.__symbolicNatBoolHits??0)+1;
        if(h[1]===LAND)return natExpr(a&b);
        if(b<=1000000n)return natExpr(a>>b);
      }
    }
    if(h?.[0]==="const"&&(h[2]??[]).length===0&&args.length===2&&
       (h[1]===BLE||h[1]===BEQ)){
      const wa=this.whnf(args[0]),wb=this.whnf(args[1]);
      const a=natCtor(wa),b=natCtor(wb);
      if(a&&b){
        this.tick();this.need("reduction");this.need("declarations");
        this.__symbolicNatBoolHits=(this.__symbolicNatBoolHits??0)+1;
        if(h[1]===BEQ){
          if(a.kind==="zero"&&b.kind==="zero")return bool(BTRUE);
          if(a.kind!==b.kind)return bool(BFALSE);
          return app2(this,h,a.pred,b.pred);
        }
        if(a.kind==="zero")return bool(BTRUE);
        if(b.kind==="zero")return bool(BFALSE);
        return app2(this,h,a.pred,b.pred);
      }
    }
  }
  return retainedWhnf.call(this,e);
};

Kernel.prototype.run=function(...args){
  this.__semanticRepairFirstRigid=null;
  this.__semanticRepairLastRigid=null;
  this.__semanticRepairHits=0;
  this.__postSemanticTicks={};\n  this.__profileMethodEdges={};
  return retainedRun.apply(this,args);
};

Kernel.prototype.tick=function(...args){
  this.__postSemanticTicks??={};
  this.__postSemanticMethodTicks??={};
  const key=String(this.currentDeclaration??"<none>");
  this.__postSemanticTicks[key]=(this.__postSemanticTicks[key]??0)+1;
  if(key===PROFILE_DECL){
    const method=(this.__postSemanticMethodStack??[]).at(-1)??"<none>";
    this.__postSemanticMethodTicks[method]=(this.__postSemanticMethodTicks[method]??0)+1;
  }
  return retainedTick.apply(this,args);
};

const PROFILE_METHODS=[
  "whnf","normal","equal","infer","proofType","instantiateDeclaration",
  "same","substitute","shift","getApp","make","appN"
];
const profileOriginals={};
for(const method of PROFILE_METHODS){
  const original=Kernel.prototype[method];
  if(typeof original!=="function")continue;
  profileOriginals[method]=original;
  Kernel.prototype[method]=function(...args){
    this.__postSemanticMethodStack??=[];
    const parent=this.__postSemanticMethodStack.at(-1)??"<root>";
    if(String(this.currentDeclaration??"<none>")===PROFILE_DECL){
      this.__profileMethodEdges??={};
      const edge=parent+"->"+method;
      this.__profileMethodEdges[edge]=(this.__profileMethodEdges[edge]??0)+1;
    }
    this.__postSemanticMethodStack.push(method);
    try{return original.apply(this,args);}
    finally{this.__postSemanticMethodStack.pop();}
  };
}

Kernel.prototype.equal=function(a,b,ctx=[]){
  try{
    return retainedEqual.call(this,a,b,ctx);
  }catch(e){
    if(e instanceof Stop && e.status===REJECT && e.message==="rigid-head-mismatch"){
      const row={
        step:this.steps,
        declaration:String(this.currentDeclaration),
        ctx_depth:ctx.length,
        left:JSON.stringify(a).slice(0,12000),
        right:JSON.stringify(b).slice(0,12000),
        stack:String(e.stack??"").split("\n").slice(0,80),
      };
      if(this.__semanticRepairFirstRigid===null)this.__semanticRepairFirstRigid=row;
      this.__semanticRepairLastRigid=row;
    }
    throw e;
  }
};

const rows=[];
for(const name of TARGETS){
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const attempts=[];
  for(const budget of BUDGETS){
    const seen=[];
    const captureRun=Kernel.prototype.run;
    Kernel.prototype.run=function(...xs){seen.push(this);return captureRun.apply(this,xs);};
    let r;
    try{
      r=P.checkExport(input,{
        semanticBudget:budget,
        inputBytes:20_000_000,
        recordLimit:400_000,
      });
    }finally{
      Kernel.prototype.run=captureRun;
    }
    const firstRigid=seen.map(k=>k.__semanticRepairFirstRigid).find(Boolean)??null;
    const lastRigid=[...seen].reverse().map(k=>k.__semanticRepairLastRigid).find(Boolean)??null;
    const symbolicHits=seen.reduce((n,k)=>n+(k.__symbolicNatBoolHits??0),0);
    const declarationTicks={};
    const methodTicks={};
    const methodEdges={};
    for(const k of seen){
      for(const [decl,n] of Object.entries(k.__postSemanticTicks??{}))
        declarationTicks[decl]=(declarationTicks[decl]??0)+n;
      for(const [method,n] of Object.entries(k.__postSemanticMethodTicks??{}))
        methodTicks[method]=(methodTicks[method]??0)+n;
      for(const [edge,n] of Object.entries(k.__profileMethodEdges??{}))
        methodEdges[edge]=(methodEdges[edge]??0)+n;
    }
    const topDeclarationTicks=Object.entries(declarationTicks)
      .map(([declaration,ticks])=>({declaration,ticks}))
      .sort((a,b)=>b.ticks-a.ticks||a.declaration.localeCompare(b.declaration))
      .slice(0,16);
    const topMethodTicks=Object.entries(methodTicks)
      .map(([method,ticks])=>({method,ticks}))
      .sort((a,b)=>b.ticks-a.ticks||a.method.localeCompare(b.method));
    const edgeRows=Object.entries(methodEdges)
      .map(([edge,count])=>({edge,count}))
      .sort((a,b)=>b.count-a.count||a.edge.localeCompare(b.edge));
    const edgeTotal=edgeRows.reduce((n,x)=>n+x.count,0);
    const top5EdgeCoverage=edgeTotal
      ? edgeRows.slice(0,5).reduce((n,x)=>n+x.count,0)/edgeTotal
      : 0;
    attempts.push({
      budget,status:r.status,reason:r.reason??null,steps:r.steps??null,
      frontier:r.frontier_declaration??null,
      symbolic_nat_bool_hits:symbolicHits,
      top_declaration_ticks:topDeclarationTicks,
      profiled_declaration:PROFILE_DECL,
      top_method_ticks_for_profiled_declaration:topMethodTicks,
      top_method_edges:edgeRows.slice(0,20),
      method_edge_total:edgeTotal,
      top5_method_edge_coverage:top5EdgeCoverage,
      first_rigid:firstRigid,
      last_rigid:lastRigid,
    });
    console.log("DEEP_LIST_SEMANTIC_REPAIR_ATTEMPT "+JSON.stringify({
      name,budget,status:r.status,reason:r.reason??null,steps:r.steps??null,
      frontier:r.frontier_declaration??null,
      symbolicHits,
      topDeclarationTicks,
      topMethodTicks,
      topMethodEdges:edgeRows.slice(0,10),
      top5EdgeCoverage,
      firstRigid,
      lastRigid,
    }));
    if(r.status==="ACCEPT"||r.status==="REJECT")break;
  }
  rows.push({name,attempts});
}
Kernel.prototype.whnf=retainedWhnf;
Kernel.prototype.equal=retainedEqual;
Kernel.prototype.run=retainedRun;
Kernel.prototype.tick=retainedTick;
for(const [method,original] of Object.entries(profileOriginals))
  Kernel.prototype[method]=original;

const terminalFrontiers=rows.map(r=>r.attempts.at(-1)?.frontier??null);
const edgeProfiles=rows.map(r=>r.attempts.at(-1)?.top_method_edges??[]);
const stableEdgeBasis=
  edgeProfiles.length===2 &&
  edgeProfiles[0][0]?.edge===edgeProfiles[1][0]?.edge &&
  edgeProfiles.every((edges,i)=>
    (edges[0]?.count??0)>=100000 &&
    (rows[i].attempts.at(-1)?.top5_method_edge_coverage??0)>=0.80
  );
const classification=stableEdgeBasis?"stable-edge-basis":"distributed-chain";
const report={
  schema:"isvalidchar-operation-chain-diagnostic-v1",
  profiled_declaration:PROFILE_DECL,
  precommit:{
    realitygraph_commit:"e06d6b29fd4b0eefe5e890a40bbafc379ae9f105",
    source_episode_run:35425682112,
    source_episode_artifact:10578428028,
    source_episode_digest:"sha256:d4c45fe366f753941a82803821f6aa758e510f2f7af06b098bb9e8f8462a6c46",
  },
  candidate:"parent->child kernel-method transition profile inside common isValidChar_UInt32 frontier",
  claim_boundary:"Diagnostic-only method nesting attribution. Wrappers observe method entry/exit and do not alter kernel semantics.",
  rows,
  terminal_frontiers:terminalFrontiers,
  edge_profiles:edgeProfiles,
  classification,
  gates:{
    no_wrong_reject:rows.every(r=>!r.attempts.some(a=>a.status==="REJECT")),
    both_remain_unknown_at_4m:rows.every(r=>r.attempts.at(-1)?.status==="UNKNOWN"&&r.attempts.at(-1)?.budget===4_000_000),
    edge_profiles_nonempty:edgeProfiles.every(r=>r.length>0),
    classification_total:["stable-edge-basis","distributed-chain"].includes(classification),
    common_terminal_frontier:terminalFrontiers.length===2&&terminalFrontiers[0]!==null&&terminalFrontiers[0]===terminalFrontiers[1],
  },
};
mkdirSync(dirname("genesis/evidence/isvalidchar-operation-chain-diagnostic-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/isvalidchar-operation-chain-diagnostic-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("ISVALIDCHAR_OPERATION_CHAIN_DIAGNOSTIC_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_ISVALIDCHAR_OPERATION_CHAIN_DIAGNOSTIC_V1");
console.log("CLASSIFICATION="+classification);
