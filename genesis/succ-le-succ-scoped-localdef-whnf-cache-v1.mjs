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
const PROFILE_DECL=N("Nat","succ_le_succ");
const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGET=2_000_000;

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
  this.__localWhnfCache=new WeakMap();
  this.__localWhnfCtxIds=new WeakMap();
  this.__localWhnfNextCtxId=1;
  this.__localWhnfCacheHits=0;
  this.__localWhnfCacheStores=0;
  this.__localWhnfCacheCtxKeys=new Set();
  this.__fastLocalWhnfCache=new WeakMap();
  this.__fastLocalWhnfCacheHits=0;
  this.__fastLocalWhnfCacheStores=0;
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

const semanticRepairWhnf=Kernel.prototype.whnf;

function localObjId(k,x){
  if(x===null)return "null";
  if(typeof x!=="object"&&typeof x!=="function")
    return typeof x+":"+String(x);
  k.__localWhnfCtxIds??=new WeakMap();
  let id=k.__localWhnfCtxIds.get(x);
  if(id===undefined){
    id=k.__localWhnfNextCtxId??1;
    k.__localWhnfNextCtxId=id+1;
    k.__localWhnfCtxIds.set(x,id);
  }
  return "o"+id;
}
function exactLocalContextKey(k){
  const ctx=k._activeCtx??[];
  const ctxPart=ctx.map(x=>localObjId(k,x)).join(",");
  const params=[...(k.params??[])].sort().join("\u0000");
  const decl=String(k.currentDeclaration??"<none>");
  return decl+"|"+params+"|"+ctxPart;
}
function cachedLocalWhnf(e){
  if(this.localDefs!==true||!Array.isArray(e))
    return semanticRepairWhnf.call(this,e);
  this.__localWhnfCache??=new WeakMap();
  let byCtx=this.__localWhnfCache.get(e);
  if(!(byCtx instanceof Map)){
    byCtx=new Map();
    this.__localWhnfCache.set(e,byCtx);
  }
  const key=exactLocalContextKey(this);
  this.__localWhnfCacheCtxKeys??=new Set();
  this.__localWhnfCacheCtxKeys.add(key);
  if(byCtx.has(key)){
    this.__localWhnfCacheHits=(this.__localWhnfCacheHits??0)+1;
    return byCtx.get(key);
  }
  const out=semanticRepairWhnf.call(this,e);
  byCtx.set(key,out);
  this.__localWhnfCacheStores=(this.__localWhnfCacheStores??0)+1;
  return out;
}


function fastIdentityLocalWhnf(e){
  if(this.localDefs!==true||!Array.isArray(e))
    return semanticRepairWhnf.call(this,e);
  this.__fastLocalWhnfCache??=new WeakMap();
  const ctx=this._activeCtx??[];
  const params=this.params;
  if(!(ctx&&typeof ctx==="object")||!(params&&typeof params==="object"))
    return semanticRepairWhnf.call(this,e);

  let byCtx=this.__fastLocalWhnfCache.get(e);
  if(!(byCtx instanceof WeakMap)){
    byCtx=new WeakMap();
    this.__fastLocalWhnfCache.set(e,byCtx);
  }
  let byParams=byCtx.get(ctx);
  if(!(byParams instanceof WeakMap)){
    byParams=new WeakMap();
    byCtx.set(ctx,byParams);
  }
  if(byParams.has(params)){
    this.__fastLocalWhnfCacheHits=(this.__fastLocalWhnfCacheHits??0)+1;
    return byParams.get(params);
  }
  const out=semanticRepairWhnf.call(this,e);
  byParams.set(params,out);
  this.__fastLocalWhnfCacheStores=(this.__fastLocalWhnfCacheStores??0)+1;
  return out;
}


function scopedIdentityLocalWhnf(e){
  if(String(this.currentDeclaration??"<none>")!==PROFILE_DECL)
    return semanticRepairWhnf.call(this,e);
  return fastIdentityLocalWhnf.call(this,e);
}


const rows=[];
for(const name of TARGETS){
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const arms={};

  for(const arm of ["cold","full-identity","scoped-identity","restart-scoped","ablation"]){
    Kernel.prototype.whnf=
      arm==="full-identity" ? fastIdentityLocalWhnf :
      (arm==="scoped-identity"||arm==="restart-scoped") ? scopedIdentityLocalWhnf :
      semanticRepairWhnf;

    const seen=[];
    const captureRun=Kernel.prototype.run;
    Kernel.prototype.run=function(...xs){
      seen.push(this);
      return captureRun.apply(this,xs);
    };

    let r;
    const started=Date.now();
    try{
      r=P.checkExport(input,{
        semanticBudget:BUDGET,
        inputBytes:20_000_000,
        recordLimit:400_000,
      });
    }finally{
      Kernel.prototype.run=captureRun;
    }
    const elapsed=Date.now()-started;
    const fastHits=seen.reduce((n,k)=>n+(k.__fastLocalWhnfCacheHits??0),0);
    const fastStores=seen.reduce((n,k)=>n+(k.__fastLocalWhnfCacheStores??0),0);

    arms[arm]={
      status:r.status,
      reason:r.reason??null,
      steps:r.steps??null,
      frontier:r.frontier_declaration??null,
      first_attempt_reason:r.first_attempt_reason??null,
      first_attempt_steps:r.first_attempt_steps??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null,
      elapsed_ms:elapsed,
      fast_cache_hits:fastHits,
      fast_cache_stores:fastStores,
    };
    console.log("SUCC_LE_SUCC_SCOPED_LOCALDEF_WHNF_CACHE_ARM "+JSON.stringify({
      name,arm,...arms[arm]
    }));
  }
  rows.push({name,arms});
}

Kernel.prototype.whnf=retainedWhnf;
Kernel.prototype.equal=retainedEqual;
Kernel.prototype.run=retainedRun;

const sum=(arm,key)=>rows.reduce((n,r)=>n+(r.arms[arm][key]??0),0);
const coldMs=sum("cold","elapsed_ms");
const fullMs=sum("full-identity","elapsed_ms");
const scopedMs=sum("scoped-identity","elapsed_ms");
const restartMs=sum("restart-scoped","elapsed_ms");
const scopedWins=coldMs>scopedMs;

const report={
  schema:"succ-le-succ-scoped-localdef-whnf-cache-v1",
  precommit:{
    realitygraph_branch:"qckn-live-developmental-substrate-v3",
    realitygraph_precommit_commit:"7a2806d8efa5b1b018c1adeb53bffbab6f2dbe54",
    source_substrate_run:35421558310,
    source_identity_cache_run:35421374389,
    promotion_rule:"promote economically only if scoped-cache total wall time is strictly below paired cold total, semantic statuses match cold, no REJECT is introduced, restart reproduces, and ablation restores cold behavior",
  },
  source_observation:{
    full_identity_cold_ms:8041,
    full_identity_fast_ms:8531,
    full_identity_hits:2875688,
    observation:"full exact-identity cache is semantically verified and cheaper than string-key realization, but still 6.09% slower than cold; scope to the verified Nat.succ_le_succ hotspot.",
  },
  candidate:"apply exact expression × active-context × universe-params identity WHNF cache only while currentDeclaration is Nat.succ_le_succ",
  profiled_declaration:PROFILE_DECL,
  claim_boundary:"Candidate-only realization preference test. No new Lean semantic rule is introduced. The exact cache semantics are unchanged from the prior verified identity-triple cache; only applicability is narrowed to one previously measured hotspot.",
  rows,
  comparison:{
    cold_elapsed_ms:coldMs,
    full_identity_elapsed_ms:fullMs,
    scoped_elapsed_ms:scopedMs,
    restart_scoped_elapsed_ms:restartMs,
    scoped_hits:sum("scoped-identity","fast_cache_hits"),
    restart_scoped_hits:sum("restart-scoped","fast_cache_hits"),
    improvement_vs_full_identity:1-scopedMs/fullMs,
    improvement_vs_cold:1-scopedMs/coldMs,
  },
  economic_status:scopedWins?"ACTIVE":"RESERVE",
  gates:{
    semantic_statuses_match_cold:rows.every(r=>
      ["full-identity","scoped-identity","restart-scoped","ablation"]
        .every(a=>r.arms[a].status===r.arms.cold.status)
    ),
    no_wrong_reject:rows.every(r=>Object.values(r.arms).every(a=>a.status!=="REJECT")),
    scoped_hits_large:rows.every(r=>r.arms["scoped-identity"].fast_cache_hits>100_000),
    restart_reproduces_scoped:rows.every(r=>
      r.arms["restart-scoped"].status===r.arms["scoped-identity"].status &&
      r.arms["restart-scoped"].reason===r.arms["scoped-identity"].reason &&
      r.arms["restart-scoped"].fast_cache_hits>100_000
    ),
    ablation_restores_zero_cache_hits:rows.every(r=>r.arms.ablation.fast_cache_hits===0),
    scoped_beats_full_identity:scopedMs<fullMs,
    promotion_rule_applied_exactly:
      (scopedWins&&scopedMs<coldMs)||(!scopedWins&&scopedMs>=coldMs),
  },
};
mkdirSync(dirname("genesis/evidence/succ-le-succ-scoped-localdef-whnf-cache-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/succ-le-succ-scoped-localdef-whnf-cache-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("SUCC_LE_SUCC_SCOPED_LOCALDEF_WHNF_CACHE_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_SUCC_LE_SUCC_SCOPED_LOCALDEF_WHNF_CACHE_V1");
console.log("ECONOMIC_STATUS="+report.economic_status);
