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
const SAMPLE_LIMIT=200_000;
let globalCaseSampleCount=0;

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
  this.__postSemanticTicks={};
  this.__profileMethodEdges={};
  this.__substituteMakeShapes=new Map();
  this.__substituteMakeCalls=0;
  this.__substituteMakeSampled=0;
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

function shallowMakeShape(args){
  const tag=String(args[0]??"<none>");
  const rest=args.slice(1).map(x=>{
    if(Array.isArray(x)){
      if(x[0]==="var")return ["var","_"];
      if(x[0]==="nat")return ["nat","_"];
      if(x[0]==="strlit")return ["strlit","_"];
      if(x[0]==="const")return ["const"];
      return [String(x[0]??"<array>")];
    }
    if(typeof x==="number")return ["number","_"];
    if(typeof x==="string")return ["string","_"];
    return [typeof x];
  });
  return JSON.stringify([tag,args.length,rest]);
}

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
      if(parent==="substitute"&&method==="make"){
        this.__substituteMakeCalls=(this.__substituteMakeCalls??0)+1;
        if(globalCaseSampleCount<SAMPLE_LIMIT){
          globalCaseSampleCount++;
          this.__substituteMakeSampled=(this.__substituteMakeSampled??0)+1;
          this.__substituteMakeShapes??=new Map();
          const key=shallowMakeShape(args);
          this.__substituteMakeShapes.set(key,(this.__substituteMakeShapes.get(key)??0)+1);
        }
      }
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
  globalCaseSampleCount=0;
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
    const makeShapes=new Map();
    let substituteMakeCalls=0;
    let substituteMakeSampled=0;
    for(const k of seen){
      for(const [decl,n] of Object.entries(k.__postSemanticTicks??{}))
        declarationTicks[decl]=(declarationTicks[decl]??0)+n;
      for(const [method,n] of Object.entries(k.__postSemanticMethodTicks??{}))
        methodTicks[method]=(methodTicks[method]??0)+n;
      for(const [edge,n] of Object.entries(k.__profileMethodEdges??{}))
        methodEdges[edge]=(methodEdges[edge]??0)+n;
      substituteMakeCalls+=k.__substituteMakeCalls??0;
      substituteMakeSampled+=k.__substituteMakeSampled??0;
      for(const [shape,n] of (k.__substituteMakeShapes??new Map()).entries())
        makeShapes.set(shape,(makeShapes.get(shape)??0)+n);
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
    const shapeRows=Array.from(makeShapes.entries())
      .map(([shape,count])=>({shape:JSON.parse(shape),count}))
      .sort((a,b)=>b.count-a.count||JSON.stringify(a.shape).localeCompare(JSON.stringify(b.shape)));
    const top8ShapeCoverage=substituteMakeSampled
      ? shapeRows.slice(0,8).reduce((n,x)=>n+x.count,0)/substituteMakeSampled
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
      substitute_make_calls:substituteMakeCalls,
      substitute_make_sampled:substituteMakeSampled,
      substitute_make_shape_class_count:shapeRows.length,
      substitute_make_top8_shape_coverage:top8ShapeCoverage,
      substitute_make_top_shapes:shapeRows.slice(0,16),
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
const shapeProfiles=rows.map(r=>r.attempts.at(-1)?.substitute_make_top_shapes??[]);
const smallStableBasis=
  shapeProfiles.length===2 &&
  shapeProfiles[0][0]?.shape!==undefined &&
  JSON.stringify(shapeProfiles[0][0]?.shape)===JSON.stringify(shapeProfiles[1][0]?.shape) &&
  rows.every(r=>{
    const a=r.attempts.at(-1);
    return a.substitute_make_shape_class_count<=16 &&
      a.substitute_make_top8_shape_coverage>=0.99 &&
      (a.substitute_make_top_shapes[0]?.count??0)>=50000;
  });
const classification=smallStableBasis?"small-stable-basis":"distributed-shapes";
const report={
  schema:"substitute-make-shape-quotient-diagnostic-v1",
  profiled_declaration:PROFILE_DECL,
  sample_limit_per_case:SAMPLE_LIMIT,
  precommit:{
    realitygraph_commit:"37de6528971f8664b622aa64aac6044013e2203f",
    source_episode_run:35425959951,
    source_episode_artifact:10579535046,
    source_episode_digest:"sha256:990769532bbffb81625a145703c8333506bd399f58951b53082033548cb38022",
  },
  candidate:"diagnostic quotient of substitute->make calls by make tag, arity and shallow child tags",
  claim_boundary:"Variable indices and literal payloads are abstracted only for diagnostic shape counting. These shape classes are not semantic equality keys and do not authorize construction reuse.",
  rows,
  terminal_frontiers:terminalFrontiers,
  shape_profiles:shapeProfiles,
  classification,
  gates:{
    no_wrong_reject:rows.every(r=>!r.attempts.some(a=>a.status==="REJECT")),
    both_remain_unknown_at_4m:rows.every(r=>r.attempts.at(-1)?.status==="UNKNOWN"&&r.attempts.at(-1)?.budget===4_000_000),
    substitute_make_edge_present:rows.every(r=>(r.attempts.at(-1)?.substitute_make_calls??0)>900000),
    sample_bound_exact:rows.every(r=>r.attempts.at(-1)?.substitute_make_sampled===SAMPLE_LIMIT),
    classification_total:["small-stable-basis","distributed-shapes"].includes(classification),
    common_terminal_frontier:terminalFrontiers.length===2&&terminalFrontiers[0]!==null&&terminalFrontiers[0]===terminalFrontiers[1],
  },
};
mkdirSync(dirname("genesis/evidence/substitute-make-shape-quotient-diagnostic-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/substitute-make-shape-quotient-diagnostic-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("SUBSTITUTE_MAKE_SHAPE_QUOTIENT_DIAGNOSTIC_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_SUBSTITUTE_MAKE_SHAPE_QUOTIENT_DIAGNOSTIC_V1");
console.log("CLASSIFICATION="+classification);
