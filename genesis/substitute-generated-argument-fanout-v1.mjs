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
const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGET=4_000_000;

const retainedWhnf=Kernel.prototype.whnf;
const retainedEqual=Kernel.prototype.equal;
const retainedRun=Kernel.prototype.run;
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
  this.__termProvenance=new WeakMap();
  this.__provenanceMethodStack=[];
  return retainedRun.apply(this,args);
};

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

const PROVENANCE_METHODS=[
  "substitute","shift","whnf","normal","instantiateDeclaration",
  "infer","equal","proofType","same","getApp","appN"
];
const provenanceOriginals={};
for(const method of PROVENANCE_METHODS){
  const original=Kernel.prototype[method];
  if(typeof original!=="function")continue;
  provenanceOriginals[method]=original;
  Kernel.prototype[method]=function(...args){
    this.__provenanceMethodStack??=[];
    this.__provenanceMethodStack.push(method);
    try{return original.apply(this,args);}
    finally{this.__provenanceMethodStack.pop();}
  };
}
const provenanceMakeOriginal=Kernel.prototype.make;
Kernel.prototype.make=function(...args){
  const parent=(this.__provenanceMethodStack??[]).at(-1)??"<root>";
  const out=provenanceMakeOriginal.apply(this,args);
  this.__termProvenance??=new WeakMap();
  if(Array.isArray(out)&&!this.__termProvenance.has(out))
    this.__termProvenance.set(out,parent);
  return out;
};

const rows=[];
function addInto(dst,src){
  if(!src||typeof src!=="object")return;
  for(const [k,v] of Object.entries(src))
    if(typeof v==="number"&&Number.isFinite(v))dst[k]=(dst[k]??0)+v;
}
function ratio(num,den){return den>0?num/den:0;}

for(const name of TARGETS){
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const seen=[];
  const captureRun=Kernel.prototype.run;
  Kernel.prototype.run=function(...xs){
    seen.push(this);
    return captureRun.apply(this,xs);
  };
  let r;
  try{
    r=P.checkExport(input,{
      semanticBudget:BUDGET,
      inputBytes:20_000_000,
      recordLimit:400_000,
    });
  }finally{
    Kernel.prototype.run=captureRun;
  }

  const binder={},sem={};
  const diag={total:0,newExpression:0,newArgument:0,newDepth:0,exactRepeat:0};
  const argFamilies=new Map();
  const argProvenance=new Map();
  const fanoutExprCounts=new Map();
  const fanoutArgCounts=new Map();
  let argFamilySampled=0;
  let substituteFanoutSampled=0;
  let kernelOrdinal=0;
  let compiledNodeHits=0,compiledSpineHits=0,allocations=0;
  for(const k of seen){
    kernelOrdinal++;
    addInto(binder,k.__binderStats);
    addInto(sem,k.__semStats);
    const q=k.__substKeyDiag;
    if(q){
      diag.total+=q.total??0;
      diag.newExpression+=q.newExpression??0;
      diag.newArgument+=q.newArgument??0;
      diag.newDepth+=q.newDepth??0;
      diag.exactRepeat+=q.exactRepeat??0;
      argFamilySampled+=q.argFamilySampled??0;
      for(const [family,n] of (q.argFamilies??new Map()).entries())
        argFamilies.set(family,(argFamilies.get(family)??0)+n);
      for(const [origin,n] of (q.argProvenance??new Map()).entries())
        argProvenance.set(origin,(argProvenance.get(origin)??0)+n);
      substituteFanoutSampled+=q.substituteFanoutSampled??0;
      for(const [id,n] of (q.fanoutExprCounts??new Map()).entries())
        fanoutExprCounts.set(kernelOrdinal+":"+id,n);
      for(const [id,n] of (q.fanoutArgCounts??new Map()).entries())
        fanoutArgCounts.set(kernelOrdinal+":"+id,n);
    }
    compiledNodeHits+=k.__compiledNodeHits??0;
    compiledSpineHits+=k.__compiledSpineHits??0;
    allocations+=k.allocations??0;
  }
  const substHits=binder.substHits??0;
  const substMisses=binder.substMisses??0;
  const familyRows=Array.from(argFamilies.entries())
    .map(([family,count])=>({family:JSON.parse(family),count}))
    .sort((a,b)=>b.count-a.count||JSON.stringify(a.family).localeCompare(JSON.stringify(b.family)));
  const top8Coverage=argFamilySampled
    ? familyRows.slice(0,8).reduce((n,x)=>n+x.count,0)/argFamilySampled
    : 0;
  const provenanceRows=Array.from(argProvenance.entries())
    .map(([origin,count])=>({origin,count}))
    .sort((a,b)=>b.count-a.count||a.origin.localeCompare(b.origin));
  const provenanceTop3Coverage=argFamilySampled
    ? provenanceRows.slice(0,3).reduce((n,x)=>n+x.count,0)/argFamilySampled
    : 0;
  const exprFanoutRows=Array.from(fanoutExprCounts.entries())
    .map(([id,count])=>({id,count}))
    .sort((a,b)=>b.count-a.count||a.id.localeCompare(b.id));
  const argFanoutRows=Array.from(fanoutArgCounts.entries())
    .map(([id,count])=>({id,count}))
    .sort((a,b)=>b.count-a.count||a.id.localeCompare(b.id));
  const top32ExprCoverage=substituteFanoutSampled
    ? exprFanoutRows.slice(0,32).reduce((n,x)=>n+x.count,0)/substituteFanoutSampled
    : 0;
  const top32ArgCoverage=substituteFanoutSampled
    ? argFanoutRows.slice(0,32).reduce((n,x)=>n+x.count,0)/substituteFanoutSampled
    : 0;
  rows.push({
    name,
    status:r.status,
    reason:r.reason??null,
    steps:r.steps??null,
    frontier:r.frontier_declaration??null,
    kernels_seen:seen.length,
    binder_stats:binder,
    semantic_cache_stats:sem,
    compiled_node_hits:compiledNodeHits,
    compiled_spine_hits:compiledSpineHits,
    allocations,
    substitution_reuse_ratio:ratio(substHits,substHits+substMisses),
    substitution_key_partition:diag,
    substitution_key_partition_fractions:{
      new_expression:ratio(diag.newExpression,diag.total),
      new_argument:ratio(diag.newArgument,diag.total),
      new_depth:ratio(diag.newDepth,diag.total),
      exact_repeat:ratio(diag.exactRepeat,diag.total),
    },
    argument_family_sampled:argFamilySampled,
    argument_family_class_count:familyRows.length,
    argument_family_top8_coverage:top8Coverage,
    argument_family_top:familyRows.slice(0,16),
    argument_provenance:provenanceRows,
    argument_provenance_top3_coverage:provenanceTop3Coverage,
    substitute_fanout_sampled:substituteFanoutSampled,
    substitute_expression_identity_count:exprFanoutRows.length,
    substitute_argument_identity_count:argFanoutRows.length,
    substitute_top32_expression_coverage:top32ExprCoverage,
    substitute_top32_argument_coverage:top32ArgCoverage,
    substitute_top_expression_counts:exprFanoutRows.slice(0,32),
    substitute_top_argument_counts:argFanoutRows.slice(0,32),
    symbolic_nat_bool_hits:seen.reduce((n,k)=>n+(k.__symbolicNatBoolHits??0),0),
  });
  console.log("SUBSTITUTE_CONSEQUENCE_ACCOUNTING_ROW="+JSON.stringify(rows.at(-1)));
}

Kernel.prototype.make=provenanceMakeOriginal;
for(const [method,original] of Object.entries(provenanceOriginals))
  Kernel.prototype[method]=original;
Kernel.prototype.whnf=retainedWhnf;
Kernel.prototype.equal=retainedEqual;
Kernel.prototype.run=retainedRun;

const hotExpression=rows.every(r=>r.substitute_top32_expression_coverage>=0.80);
const hotArgument=rows.every(r=>r.substitute_top32_argument_coverage>=0.80);
let classification;
if(hotExpression&&hotArgument)classification="bilateral-hot-basis";
else if(hotExpression)classification="hot-expression-basis";
else if(hotArgument)classification="hot-argument-basis";
else classification="diffuse-cross-product";

const report={
  schema:"substitute-generated-argument-fanout-v1",
  precommit:{
    realitygraph_commit:"6842cb48501c6ee40825b70adcf424c68d5a1c4f",
    source_episode_run:35434165106,
    source_episode_artifact:10581302233,
    source_episode_digest:"sha256:094d665aefdd209b0265d06a590e3e239aa9007c91abb706c566cb8b9b0bfe36",
  },
  semantic_context:"qualified exact symbolic Nat repair plus substitution argument provenance instrumentation",
  candidate:"measure identity fanout only for newArgument events whose argument object provenance is substitute",
  claim_boundary:"Diagnostic runtime-local identity concentration only. Distinct expressions and arguments remain semantically distinct; concentration licenses only a prospective representation experiment.",
  rows,
  classification,
  gates:{
    no_wrong_reject:rows.every(r=>r.status!=="REJECT"),
    both_unknown_at_4m:rows.every(r=>r.status==="UNKNOWN"&&r.steps===4_000_001),
    substitute_origin_events_present:rows.every(r=>r.substitute_fanout_sampled>30_000),
    fanout_partitions_exact:rows.every(r=>{
      const a=r.substitute_top_argument_counts.reduce((n,x)=>n+x.count,0);
      const e=r.substitute_top_expression_counts.reduce((n,x)=>n+x.count,0);
      return a<=r.substitute_fanout_sampled&&e<=r.substitute_fanout_sampled;
    }),
    classification_total:["bilateral-hot-basis","hot-expression-basis","hot-argument-basis","diffuse-cross-product"].includes(classification),
  },
};
mkdirSync(dirname("genesis/evidence/substitute-generated-argument-fanout-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/substitute-generated-argument-fanout-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("SUBSTITUTE_GENERATED_ARGUMENT_FANOUT_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_SUBSTITUTE_GENERATED_ARGUMENT_FANOUT_V1");
console.log("CLASSIFICATION="+classification);
