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



function guardOnlyWhnf(e){
  if(String(this.currentDeclaration??"<none>")===PROFILE_DECL)
    this.__guardOnlyHits=(this.__guardOnlyHits??0)+1;
  return semanticRepairWhnf.call(this,e);
}

function lookupOnlyWhnf(e){
  if(String(this.currentDeclaration??"<none>")!==PROFILE_DECL)
    return semanticRepairWhnf.call(this,e);
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
  if(byParams.has(params))
    this.__lookupOnlyHits=(this.__lookupOnlyHits??0)+1;
  else
    this.__lookupOnlyMisses=(this.__lookupOnlyMisses??0)+1;

  const out=semanticRepairWhnf.call(this,e);
  if(!byParams.has(params))byParams.set(params,out);
  return out;
}

function median(values){
  const xs=[...values].sort((a,b)=>a-b);
  const n=xs.length;
  return n%2 ? xs[(n-1)/2] : (xs[n/2-1]+xs[n/2])/2;
}

const REPETITIONS=3;
const ARMS=["cold","declaration-guard-only","lookup-only","scoped-cache"];
const rows=[];

for(const name of TARGETS){
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const arms={};

  for(const arm of ARMS){
    const reps=[];
    for(let rep=0;rep<REPETITIONS;rep++){
      Kernel.prototype.whnf=
        arm==="declaration-guard-only" ? guardOnlyWhnf :
        arm==="lookup-only" ? lookupOnlyWhnf :
        arm==="scoped-cache" ? scopedIdentityLocalWhnf :
        semanticRepairWhnf;

      const seen=[];
      const captureRun=Kernel.prototype.run;
      Kernel.prototype.run=function(...xs){
        this.__guardOnlyHits=0;
        this.__lookupOnlyHits=0;
        this.__lookupOnlyMisses=0;
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
      reps.push({
        rep,
        status:r.status,
        reason:r.reason??null,
        steps:r.steps??null,
        elapsed_ms:elapsed,
        guard_only_hits:seen.reduce((n,k)=>n+(k.__guardOnlyHits??0),0),
        lookup_only_hits:seen.reduce((n,k)=>n+(k.__lookupOnlyHits??0),0),
        lookup_only_misses:seen.reduce((n,k)=>n+(k.__lookupOnlyMisses??0),0),
        scoped_cache_hits:seen.reduce((n,k)=>n+(k.__fastLocalWhnfCacheHits??0),0),
        scoped_cache_stores:seen.reduce((n,k)=>n+(k.__fastLocalWhnfCacheStores??0),0),
      });
      console.log("LOCALDEF_WHNF_OVERHEAD_REP "+JSON.stringify({
        name,arm,...reps.at(-1)
      }));
    }

    arms[arm]={
      repetitions:reps,
      median_elapsed_ms:median(reps.map(r=>r.elapsed_ms)),
      statuses:[...new Set(reps.map(r=>r.status))],
      reasons:[...new Set(reps.map(r=>r.reason))],
      median_guard_only_hits:median(reps.map(r=>r.guard_only_hits)),
      median_lookup_only_hits:median(reps.map(r=>r.lookup_only_hits)),
      median_lookup_only_misses:median(reps.map(r=>r.lookup_only_misses)),
      median_scoped_cache_hits:median(reps.map(r=>r.scoped_cache_hits)),
      median_scoped_cache_stores:median(reps.map(r=>r.scoped_cache_stores)),
    };
  }
  rows.push({name,arms});
}

Kernel.prototype.whnf=retainedWhnf;
Kernel.prototype.equal=retainedEqual;
Kernel.prototype.run=retainedRun;

const totalMedian=arm=>rows.reduce((n,r)=>n+r.arms[arm].median_elapsed_ms,0);
const coldMs=totalMedian("cold");
const guardMs=totalMedian("declaration-guard-only");
const lookupMs=totalMedian("lookup-only");
const scopedMs=totalMedian("scoped-cache");

const classification={
  reuse_gross_beneficial:lookupMs>scopedMs,
  guard_overhead_positive:guardMs>coldMs,
  lookup_overhead_positive:lookupMs>guardMs,
  net_win:scopedMs<coldMs,
};

let nextRoute;
if(classification.net_win)
  nextRoute="promote-scoped-cache";
else if(classification.reuse_gross_beneficial)
  nextRoute="reduce-cache-lookup-overhead";
else
  nextRoute="pivot-away-from-whnf-memoization";

const report={
  schema:"localdef-whnf-cache-overhead-decomposition-v1",
  precommit:{
    realitygraph_commit:"596038b0d96fcda4780056be10bc69766bbcdaf7",
    source_episode_run:35422069761,
    source_episode_artifact:10577249725,
    source_episode_digest:"sha256:4d2b1bb252c0865738c4ceaefac82c0b3708a5d523c07081c0edf2e4b6dccf1f",
    repetitions_per_case:REPETITIONS,
    classification_rule:{
      reuse_gross_beneficial:"lookup-only median > scoped-cache median",
      guard_overhead_positive:"guard-only median > cold median",
      lookup_overhead_positive:"lookup-only median > guard-only median",
      net_win:"scoped-cache median < cold median",
    },
  },
  candidate:"decompose cold versus declaration guard versus exact identity lookup versus verified consequence reuse at the Nat.succ_le_succ hotspot",
  claim_boundary:"Diagnostic-only performance decomposition using the already qualified exact scoped cache semantics. No new conversion rule or semantic cache authority is introduced. Timings are paired medians over three repetitions per case on one GitHub runner.",
  rows,
  totals_ms:{
    cold:coldMs,
    declaration_guard_only:guardMs,
    lookup_only:lookupMs,
    scoped_cache:scopedMs,
  },
  deltas_ms:{
    guard_minus_cold:guardMs-coldMs,
    lookup_minus_guard:lookupMs-guardMs,
    lookup_minus_scoped:lookupMs-scopedMs,
    scoped_minus_cold:scopedMs-coldMs,
  },
  classification,
  next_route:nextRoute,
  gates:{
    all_arms_semantically_match_cold:rows.every(r=>
      ARMS.every(a=>
        r.arms[a].statuses.length===1 &&
        r.arms[a].statuses[0]===r.arms.cold.statuses[0]
      )
    ),
    no_wrong_reject:rows.every(r=>ARMS.every(a=>!r.arms[a].statuses.includes("REJECT"))),
    three_repetitions_each:rows.every(r=>ARMS.every(a=>r.arms[a].repetitions.length===REPETITIONS)),
    lookup_path_exercised:rows.every(r=>r.arms["lookup-only"].median_lookup_only_hits>100_000),
    scoped_reuse_exercised:rows.every(r=>r.arms["scoped-cache"].median_scoped_cache_hits>100_000),
    classification_total:typeof nextRoute==="string"&&nextRoute.length>0,
  },
};
mkdirSync(dirname("genesis/evidence/localdef-whnf-cache-overhead-decomposition-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/localdef-whnf-cache-overhead-decomposition-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("LOCALDEF_WHNF_CACHE_OVERHEAD_DECOMPOSITION_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_LOCALDEF_WHNF_CACHE_OVERHEAD_DECOMPOSITION_V1");
console.log("NEXT_ROUTE="+nextRoute);
