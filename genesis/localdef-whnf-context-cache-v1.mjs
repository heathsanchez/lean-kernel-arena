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


const rows=[];
for(const name of TARGETS){
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const arms={};

  for(const arm of ["cold","warm","restart","ablation"]){
    Kernel.prototype.whnf=(arm==="warm"||arm==="restart")
      ?cachedLocalWhnf
      :semanticRepairWhnf;

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

    const cacheHits=seen.reduce((n,k)=>n+(k.__localWhnfCacheHits??0),0);
    const cacheStores=seen.reduce((n,k)=>n+(k.__localWhnfCacheStores??0),0);
    const contextKeys=new Set();
    for(const k of seen)
      for(const key of (k.__localWhnfCacheCtxKeys??[]))contextKeys.add(key);

    arms[arm]={
      status:r.status,
      reason:r.reason??null,
      steps:r.steps??null,
      frontier:r.frontier_declaration??null,
      first_attempt_reason:r.first_attempt_reason??null,
      first_attempt_steps:r.first_attempt_steps??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null,
      elapsed_ms:Date.now()-started,
      local_whnf_cache_hits:cacheHits,
      local_whnf_cache_stores:cacheStores,
      local_whnf_context_keys:contextKeys.size,
    };
    console.log("LOCALDEF_WHNF_CONTEXT_CACHE_ARM "+JSON.stringify({
      name,arm,...arms[arm]
    }));
  }
  rows.push({name,arms});
}

Kernel.prototype.whnf=semanticRepairWhnf;
Kernel.prototype.whnf=retainedWhnf;
Kernel.prototype.equal=retainedEqual;
Kernel.prototype.run=retainedRun;

const report={
  schema:"localdef-whnf-context-cache-v1",
  candidate:"successful WHNF reuse keyed by exact expression identity, exact local-context entry identities, universe params, and current declaration",
  source_observation:{
    run_id:35420232683,
    artifact_id:10577696503,
    artifact_digest:"sha256:b2feeb57d2acbf8426a2a533319f4e263ac08f343e1dbdd2e06c04c4b2607d28",
    identity_repeat_fraction:[0.9997687781522181,0.999768778742974],
  },
  claim_boundary:"Candidate-only exact-identity local-definition WHNF consequence cache. Only successful WHNF results are retained, under an exact declaration/params/local-context identity key. No failure, UNKNOWN, REJECT, structural equality, theorem, or new conversion rule is cached.",
  rows,
  gates:{
    cold_unknown:rows.every(r=>r.arms.cold.status==="UNKNOWN"),
    no_wrong_reject:rows.every(r=>Object.values(r.arms).every(a=>a.status!=="REJECT")),
    warm_cache_hits_large:rows.every(r=>r.arms.warm.local_whnf_cache_hits>100_000),
    restart_reproduces_warm:rows.every(r=>
      r.arms.restart.status===r.arms.warm.status &&
      r.arms.restart.reason===r.arms.warm.reason &&
      r.arms.restart.local_whnf_cache_hits>100_000
    ),
    ablation_restores_cold_cache_behavior:rows.every(r=>
      r.arms.ablation.local_whnf_cache_hits===0 &&
      r.arms.cold.local_whnf_cache_hits===0
    ),
  },
};
mkdirSync(dirname("genesis/evidence/localdef-whnf-context-cache-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/localdef-whnf-context-cache-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("LOCALDEF_WHNF_CONTEXT_CACHE_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_LOCALDEF_WHNF_CONTEXT_CACHE_V1");
