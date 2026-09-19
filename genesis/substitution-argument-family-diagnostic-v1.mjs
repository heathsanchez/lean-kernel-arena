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
  let argFamilySampled=0;
  let compiledNodeHits=0,compiledSpineHits=0,allocations=0;
  for(const k of seen){
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
    symbolic_nat_bool_hits:seen.reduce((n,k)=>n+(k.__symbolicNatBoolHits??0),0),
  });
  console.log("SUBSTITUTE_CONSEQUENCE_ACCOUNTING_ROW="+JSON.stringify(rows.at(-1)));
}

Kernel.prototype.whnf=retainedWhnf;
Kernel.prototype.equal=retainedEqual;
Kernel.prototype.run=retainedRun;

const familyProfiles=rows.map(r=>r.argument_family_top);
const sameDominant=
  familyProfiles.length===2 &&
  familyProfiles[0][0]?.family!==undefined &&
  JSON.stringify(familyProfiles[0][0].family)===JSON.stringify(familyProfiles[1][0].family);
const smallStable=
  sameDominant &&
  rows.every(r=>
    r.argument_family_class_count<=16 &&
    r.argument_family_top8_coverage>=0.95 &&
    (r.argument_family_top[0]?.count??0)>=50_000
  );
const stableHeavyTail=
  !smallStable &&
  sameDominant &&
  rows.every(r=>r.argument_family_top8_coverage>=0.70);
const classification=
  smallStable ? "small-stable-family" :
  stableHeavyTail ? "stable-heavy-tail" :
  "distributed-arguments";

const report={
  schema:"substitution-argument-family-diagnostic-v1",
  precommit:{
    realitygraph_commit:"25cb163784828bb8fab9cde181282342b3c9bb00",
    source_episode_run:35433372707,
    source_episode_artifact:10581401124,
    source_episode_digest:"sha256:782d8242750736893f4e00f714458b787702b84a35a8b389c53f53ee2f767383",
  },
  semantic_context:"qualified exact symbolic Nat repair plus exact substitution-key diagnostic instrumentation",
  candidate:"classify new substitution-argument identities by a shallow application/head/arity family without reusing across arguments",
  claim_boundary:"Diagnostic family counting only. Distinct substitution arguments remain semantically distinct; no cross-argument cache reuse, structural equality or substitution quotient is authorized.",
  rows,
  family_profiles:familyProfiles,
  classification,
  gates:{
    no_wrong_reject:rows.every(r=>r.status!=="REJECT"),
    both_unknown_at_4m:rows.every(r=>r.status==="UNKNOWN"&&r.steps===4_000_001),
    new_argument_events_present:rows.every(r=>r.substitution_key_partition.newArgument>1_000_000),
    bounded_family_sample:rows.every(r=>r.argument_family_sampled>50_000&&r.argument_family_sampled<=200_000),
    family_counts_exact:rows.every(r=>r.argument_family_top.reduce((n,x)=>n+x.count,0)<=r.argument_family_sampled),
    classification_total:["small-stable-family","stable-heavy-tail","distributed-arguments"].includes(classification),
  },
};
mkdirSync(dirname("genesis/evidence/substitution-argument-family-diagnostic-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/substitution-argument-family-diagnostic-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("SUBSTITUTION_ARGUMENT_FAMILY_DIAGNOSTIC_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_SUBSTITUTION_ARGUMENT_FAMILY_DIAGNOSTIC_V1");
console.log("CLASSIFICATION="+classification);
