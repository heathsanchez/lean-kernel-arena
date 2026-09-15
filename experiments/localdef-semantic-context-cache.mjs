// Prospective LocalDef semantic-context consequence cache.
//
// Hypothesis:
// retained caches key complete contexts by context-entry object identity. LocalDef
// entries are freshly allocated wrapper objects {__localDef,type,value}; repeated
// execution can therefore miss an otherwise exact consequence even when the
// binder's exact type and exact value term are unchanged.
//
// This separator erases ONLY that wrapper identity from cache keys:
//   ordinary binder  -> exact entry object identity
//   LocalDef binder  -> exact type object identity + exact value object identity
// Binder order and context length remain exact. Terms are not normalized,
// alpha-renamed, hashed approximately, or compared semantically.
//
// Only successful infer/equal completions are cached. No failures, UNKNOWNs,
// REJECTs, WHNF results, or declarations are cached.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=[
  "import io,tarfile,json,sys",
  "data=sys.stdin.buffer.read();rows=[]",
  "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
  "  for m in a:",
  "    p=m.name.split('/')",
  "    if not m.isfile() or not m.name.endswith('.ndjson') or m.size>2000000: continue",
  "    e='ACCEPT' if 'good' in p else 'REJECT' if 'bad' in p else None",
  "    if e: rows.append({'name':m.name,'expected':e,'input':a.extractfile(m).read().decode('utf-8')})",
  "print(json.dumps(rows))"
].join("\\n");
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==188) throw new Error("Arena row count changed");
const focusRows=rows.filter(r=>r.name.endsWith("good/perf/fueled-chain.ndjson"));
if(focusRows.length!==1) throw new Error("fueled-chain missing");

const proto=K.Kernel.prototype;
const retainedRun=proto.run;
const retainedInfer=proto.infer;
const retainedEqual=proto.equal;

const stats={
  ctxKeys:0,localEntries:0,
  inferQueries:0,inferHits:0,inferStores:0,
  equalQueries:0,equalHits:0,equalStores:0
};

function objectId(k,x){
  k.__semCtxIds??=new WeakMap(); k.__semCtxNextId??=1;
  if(x===null || (typeof x!=="object"&&typeof x!=="function"))
    return typeof x+":"+String(x);
  let id=k.__semCtxIds.get(x);
  if(id!==undefined) return "o"+id;
  id=k.__semCtxNextId++; k.__semCtxIds.set(x,id); return "o"+id;
}

function ctxKey(k,ctx){
  stats.ctxKeys++;
  if(!ctx?.length) return "";
  const parts=new Array(ctx.length);
  for(let i=0;i<ctx.length;i++){
    const x=ctx[i];
    if(x?.__localDef===true){
      stats.localEntries++;
      parts[i]="D:"+objectId(k,x.type)+":"+objectId(k,x.value);
    }else{
      parts[i]="T:"+objectId(k,x);
    }
  }
  return parts.join("|");
}

function equalSlot(k,a,b){
  k.__semCtxEqual??=new WeakMap();
  let byA=k.__semCtxEqual.get(a);
  if(!byA){byA=new WeakMap();k.__semCtxEqual.set(a,byA);}
  let byB=byA.get(b);
  if(!byB){byB=new Set();byA.set(b,byB);}
  return byB;
}

function install(mode){
  proto.run=retainedRun;
  proto.infer=retainedInfer;
  proto.equal=retainedEqual;
  if(mode==="baseline") return;

  proto.run=function(...args){
    this.__semCtxIds=new WeakMap();this.__semCtxNextId=1;
    this.__semCtxInfer=new WeakMap();this.__semCtxEqual=new WeakMap();
    return retainedRun.apply(this,args);
  };

  if(mode==="infer"||mode==="both"){
    proto.infer=function(e,ctx=[]){
      if(this.localDefs!==true || !Array.isArray(e))
        return retainedInfer.call(this,e,ctx);
      stats.inferQueries++;
      this.__semCtxInfer??=new WeakMap();
      let byCtx=this.__semCtxInfer.get(e);
      if(!byCtx){byCtx=new Map();this.__semCtxInfer.set(e,byCtx);}
      const key=ctxKey(this,ctx);
      if(byCtx.has(key)){stats.inferHits++;return byCtx.get(key);}
      const out=retainedInfer.call(this,e,ctx);
      byCtx.set(key,out);stats.inferStores++;
      return out;
    };
  }

  if(mode==="equal"||mode==="both"){
    proto.equal=function(a,b,ctx=[]){
      if(this.localDefs!==true || !Array.isArray(a)||!Array.isArray(b))
        return retainedEqual.call(this,a,b,ctx);
      stats.equalQueries++;
      const key=ctxKey(this,ctx);
      const slot=equalSlot(this,a,b);
      if(slot.has(key)){stats.equalHits++;return;}
      const out=retainedEqual.call(this,a,b,ctx);
      slot.add(key);equalSlot(this,b,a).add(key);stats.equalStores++;
      return out;
    };
  }
}

function evalRows(mode,subset,budget){
  install(mode);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null,
      fallback_mode:r.fallback_mode??null,fallback_attempt_reason:r.fallback_attempt_reason??null});
  }
  const d={};for(const k of Object.keys(before)) d[k]=stats[k]-before[k];
  return {mode,budget,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results};
}

const focus={
  baseline:evalRows("baseline",focusRows,1_000_000),
  infer:evalRows("infer",focusRows,1_000_000),
  equal:evalRows("equal",focusRows,1_000_000),
  both:evalRows("both",focusRows,1_000_000)
};
for(const x of Object.values(focus)) if(x.wrong) throw new Error("focus wrong verdict");

function rank(x){
  const r=x.results[0];
  if(r.status==="ACCEPT") return [-1,r.steps??0,r.constructed??0];
  return [0,r.constructed??Number.MAX_SAFE_INTEGER,x.elapsed_ms];
}
const candidates=[focus.infer,focus.equal,focus.both].sort((a,b)=>{
  const x=rank(a),y=rank(b);
  for(let i=0;i<x.length;i++) if(x[i]!==y[i]) return x[i]-y[i];
  return a.mode.localeCompare(b.mode);
});
const winnerMode=candidates[0].mode;
let winner=candidates[0];

let cliff=null;
if(winner.results[0]?.status!=="ACCEPT"){
  cliff=evalRows(winnerMode,focusRows,2_000_000);
  if(cliff.wrong) throw new Error("cliff wrong verdict");
  if(cliff.results[0]?.status==="ACCEPT") winner=cliff;
}

let full=null;
if(winner.results[0]?.status==="ACCEPT"){
  const candidate=evalRows(winnerMode,rows,1_000_000);
  const baseline=evalRows("baseline",rows,1_000_000);
  if(candidate.wrong||baseline.wrong) throw new Error("full wrong verdict");
  let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],c=candidate.results[i];
    if(b.status!=="UNKNOWN"&&c.status!==b.status){
      protectedChanged++;
      regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
    }
    if(b.status==="UNKNOWN"){
      if(c.status!=="UNKNOWN"&&c.status===c.expected)
        resolved.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
      else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,frontier_declaration:c.frontier_declaration});
    }
  }
  full={
    baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
    candidate:{mode:winnerMode,counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
      elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
    lawful:candidate.wrong===0&&protectedChanged===0,
    promotable:candidate.wrong===0&&protectedChanged===0&&resolved.length>0
  };
}

install("baseline");
const report={
  arena_sha256:sha,
  focus,
  winner_mode:winnerMode,
  cliff,
  full,
  claim_boundary:"Execution consequence reuse only. Cache keys preserve exact term identities, exact binder order and exact ordinary binder identities. For LocalDef context entries only, the transient wrapper object's identity is replaced by the exact identity pair (entry.type, entry.value). Only successful exact inference/equality consequences are reused; no failed comparison, WHNF result, reduction, typing or equality rule is added."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/localdef-semantic-context-cache.json",import.meta.url),JSON.stringify(report,null,2)+"\\n");
console.log("LOCALDEF_SEMANTIC_CONTEXT_CACHE "+JSON.stringify(report));
