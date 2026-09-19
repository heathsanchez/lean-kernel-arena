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
const retainedSubstitute=Kernel.prototype.substitute;
const retainedMake=Kernel.prototype.make;
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
  this.__subMakeDepth=0;
  this.__subMakeStats={
    total:0,compiledHit:0,lowerReuse:0,freshAllocation:0,other:0,
    byTag:{}
  };
  return retainedRun.apply(this,args);
};

Kernel.prototype.substitute=function(...args){
  this.__subMakeDepth=(this.__subMakeDepth??0)+1;
  try{return retainedSubstitute.apply(this,args);}
  finally{this.__subMakeDepth--;}
};

Kernel.prototype.make=function(...args){
  if(!(this.__subMakeDepth>0))return retainedMake.apply(this,args);
  this.__subMakeStats??={total:0,compiledHit:0,lowerReuse:0,freshAllocation:0,other:0,byTag:{}};
  const s=this.__subMakeStats;
  const tag=String(args[0]??"<none>");
  const beforeHits=this.__compiledNodeHits??0;
  const beforeAlloc=this.allocations??0;
  const out=retainedMake.apply(this,args);
  const afterHits=this.__compiledNodeHits??0;
  const afterAlloc=this.allocations??0;
  s.total++;
  const row=s.byTag[tag]??={total:0,compiledHit:0,lowerReuse:0,freshAllocation:0,other:0};
  row.total++;
  if(afterHits>beforeHits){s.compiledHit++;row.compiledHit++;}
  else if(afterAlloc>beforeAlloc){s.freshAllocation++;row.freshAllocation++;}
  else if(afterAlloc===beforeAlloc){s.lowerReuse++;row.lowerReuse++;}
  else{s.other++;row.other++;}
  s.byTag[tag]=row;
  return out;
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
  const subMake={total:0,compiledHit:0,lowerReuse:0,freshAllocation:0,other:0,byTag:{}};
  let compiledNodeHits=0,compiledSpineHits=0,allocations=0;
  for(const k of seen){
    addInto(binder,k.__binderStats);
    addInto(sem,k.__semStats);
    const q=k.__subMakeStats;
    if(q){
      for(const key of ["total","compiledHit","lowerReuse","freshAllocation","other"])
        subMake[key]+=q[key]??0;
      for(const [tag,row] of Object.entries(q.byTag??{})){
        const t=subMake.byTag[tag]??={total:0,compiledHit:0,lowerReuse:0,freshAllocation:0,other:0};
        for(const key of ["total","compiledHit","lowerReuse","freshAllocation","other"])
          t[key]+=row[key]??0;
        subMake.byTag[tag]=t;
      }
    }
    compiledNodeHits+=k.__compiledNodeHits??0;
    compiledSpineHits+=k.__compiledSpineHits??0;
    allocations+=k.allocations??0;
  }
  const substHits=binder.substHits??0;
  const substMisses=binder.substMisses??0;
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
    substitute_make_stats:subMake,
    substitute_make_reuse_fraction:ratio(subMake.compiledHit+subMake.lowerReuse,subMake.total),
    substitute_make_fresh_fraction:ratio(subMake.freshAllocation,subMake.total),
    substitute_make_by_tag:Object.entries(subMake.byTag)
      .map(([tag,row])=>({tag,...row,fresh_fraction:ratio(row.freshAllocation,row.total)}))
      .sort((a,b)=>b.freshAllocation-a.freshAllocation||a.tag.localeCompare(b.tag)),
    substitution_reuse_ratio:ratio(substHits,substHits+substMisses),
    symbolic_nat_bool_hits:seen.reduce((n,k)=>n+(k.__symbolicNatBoolHits??0),0),
  });
  console.log("SUBSTITUTE_CONSEQUENCE_ACCOUNTING_ROW="+JSON.stringify(rows.at(-1)));
}

Kernel.prototype.make=retainedMake;
Kernel.prototype.substitute=retainedSubstitute;
Kernel.prototype.whnf=retainedWhnf;
Kernel.prototype.equal=retainedEqual;
Kernel.prototype.run=retainedRun;

const reuseSaturated=rows.every(r=>r.substitute_make_reuse_fraction>=0.80);
const allocationDominant=rows.every(r=>r.substitute_make_fresh_fraction>=0.50);
const classification=reuseSaturated?"reuse-saturated":allocationDominant?"allocation-dominant":"mixed";

const report={
  schema:"substitute-node-reuse-accounting-v1",
  precommit:{
    realitygraph_commit:"328d597b2836846e67ff527acd1434311792cc11",
    source_episode_run:35434872033,
    source_episode_artifact:10582093003,
    source_episode_digest:"sha256:841e41d66e4628e33060503398b27039bc3d2d6845aa93a471a8830454632419",
  },
  semantic_context:"qualified exact symbolic Nat repair with current compiled node reuse, structural sharing and exact binder transport",
  candidate:"account existing compiled-node hits, lower-layer no-allocation reuse and fresh allocations for make calls executed inside substitute",
  claim_boundary:"Diagnostic accounting only. The wrapper observes existing counters around make calls inside substitute and does not change make, structural sharing, substitution, cache admission or semantic authority.",
  rows,
  classification,
  gates:{
    no_wrong_reject:rows.every(r=>r.status!=="REJECT"),
    both_unknown_at_4m:rows.every(r=>r.status==="UNKNOWN"&&r.steps===4_000_001),
    substitute_make_present:rows.every(r=>r.substitute_make_stats.total>100_000),
    accounting_exact:rows.every(r=>{
      const q=r.substitute_make_stats;
      return q.total===q.compiledHit+q.lowerReuse+q.freshAllocation+q.other;
    }),
    no_unclassified_calls:rows.every(r=>r.substitute_make_stats.other===0),
    classification_total:["reuse-saturated","allocation-dominant","mixed"].includes(classification),
  },
};
mkdirSync(dirname("genesis/evidence/substitute-node-reuse-accounting-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/substitute-node-reuse-accounting-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("SUBSTITUTE_NODE_REUSE_ACCOUNTING_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_SUBSTITUTE_NODE_REUSE_ACCOUNTING_V1");
console.log("CLASSIFICATION="+classification);
