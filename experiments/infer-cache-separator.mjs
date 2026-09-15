// Prospective separator: exact inference consequence reuse.
// app-lam deliberately presents the same Expr object repeatedly at the same
// binder context. Inference is deterministic under a fixed exact context and
// monotonic successful environment; cache successes only, never failures.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==188)throw new Error("Arena row count changed");

const proto=K.Kernel.prototype, retainedRun=proto.run, retainedInfer=proto.infer;

function objectId(k,x){
  k.__inferCtxIds??=new WeakMap();k.__nextInferCtxId??=1;
  let id=k.__inferCtxIds.get(x);
  if(id!==undefined)return id;
  id=k.__nextInferCtxId++;
  k.__inferCtxIds.set(x,id);
  return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length)return "";
  const parts=new Array(ctx.length);
  for(let i=0;i<ctx.length;i++){
    const x=ctx[i];
    parts[i]=(x!==null&&(typeof x==="object"||typeof x==="function"))
      ?"o"+objectId(k,x)
      :typeof x+":"+String(x);
  }
  return parts.join(",");
}
function install(mode){
  proto.run=retainedRun;proto.infer=retainedInfer;
  if(mode==="baseline")return;
  proto.run=function(...args){
    this.__inferCache=new WeakMap();
    this.__inferCtxIds=new WeakMap();
    this.__nextInferCtxId=1;
    this.__inferCacheHits=0;
    return retainedRun.apply(this,args);
  };
  proto.infer=function(e,ctx=[]){
    if(!Array.isArray(e))return retainedInfer.call(this,e,ctx);
    this.__inferCache??=new WeakMap();
    let byCtx=this.__inferCache.get(e);
    if(!(byCtx instanceof Map)){byCtx=new Map();this.__inferCache.set(e,byCtx);}
    const key=ctxKey(this,ctx);
    if(byCtx.has(key)){
      this.__inferCacheHits=(this.__inferCacheHits??0)+1;
      if(mode==="tick")this.tick();
      return byCtx.get(key);
    }
    const out=retainedInfer.call(this,e,ctx);
    byCtx.set(key,out);
    return out;
  };
}

const budget=1_000_000;
function evaluate(mode){
  install(mode);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0,totalHits=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,fallback_mode:r.fallback_mode??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,totalHits,elapsed_ms:Date.now()-t0,results};
}
const variants=["baseline","tick","free"].map(evaluate);
proto.run=retainedRun;proto.infer=retainedInfer;
const baseline=variants[0];
if(baseline.wrong)throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
const summaries=[];
for(const v of variants){
  let protectedChanged=0,resolved=0;const resolvedCases=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status){protectedChanged++;regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});}
    if(residual.has(r.name)){
      if(r.status!=="UNKNOWN"){
        if(r.status!==r.expected)throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
        resolved++;resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
      }else remaining.push({name:r.name,reason:r.reason,steps:r.steps});
    }
  }
  const s={mode:v.mode,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,elapsed_ms:v.elapsed_ms,resolvedCases,regressions,remaining};
  summaries.push(s);console.log("INFER_CACHE_VARIANT "+JSON.stringify(s));
}
const lawful=summaries.filter(s=>s.mode!=="baseline"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0)
  .sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),lawful_candidates:lawful.map(x=>x.mode),provisional_winner:lawful[0]?.mode??null,
  claim_boundary:"Execution compilation only. Successful inference of the exact expression under the complete exact binder/local-definition context is reused. Failures are never cached; no typing or conversion rule changes."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/infer-cache-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("INFER_CACHE_CONCLUSION "+JSON.stringify(conclusion));
