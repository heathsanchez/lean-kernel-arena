// Prospective separator forced by the post-sharing hotspot atlas.
// Freeze three exact successful-operation caches before outcomes:
// G = app-spine decomposition, V = syntax validation by universe-parameter state,
// I = universe instantiation. No semantic rule changes.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "./kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("./evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");

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
if(rows.length!==188) throw new Error("Arena row count changed: "+rows.length);

const proto=K.Kernel.prototype;
const originalRun=proto.run, originalGetApp=proto.getApp;
const originalValidate=proto.validate, originalInstantiate=proto.instantiateDeclaration;

function install(mask) {
  proto.run=originalRun; proto.getApp=originalGetApp;
  proto.validate=originalValidate; proto.instantiateDeclaration=originalInstantiate;

  proto.run=function(...args) {
    this.__getAppCache=new WeakMap();
    this.__validateCache=new WeakMap();
    this.__instantiateCache=new WeakMap();
    return originalRun.apply(this,args);
  };

  if(mask.includes("G")) {
    proto.getApp=function(e) {
      if(Array.isArray(e)) {
        const hit=this.__getAppCache?.get(e);
        if(hit!==undefined) { this.tick(); return hit; }
      }
      const out=originalGetApp.call(this,e);
      if(Array.isArray(e)) this.__getAppCache?.set(e,out);
      return out;
    };
  }

  if(mask.includes("V")) {
    proto.validate=function(e) {
      if(Array.isArray(e)) {
        let states=this.__validateCache?.get(e);
        if(!states) { states=new Set(); this.__validateCache?.set(e,states); }
        const state=JSON.stringify([...this.params]);
        if(states.has(state)) { this.tick(); return; }
        const out=originalValidate.call(this,e);
        states.add(state); // cache completed successful validation only
        return out;
      }
      return originalValidate.call(this,e);
    };
  }

  if(mask.includes("I")) {
    proto.instantiateDeclaration=function(ref,term) {
      if(Array.isArray(term)) {
        let m=this.__instantiateCache?.get(term);
        if(!m) { m=new Map(); this.__instantiateCache?.set(term,m); }
        const key=JSON.stringify(ref);
        if(m.has(key)) { this.tick(); return m.get(key); }
        const out=originalInstantiate.call(this,ref,term);
        m.set(key,out); // cache completed successful instantiation only
        return out;
      }
      return originalInstantiate.call(this,ref,term);
    };
  }
}

const budget=1_000_000;
function evaluate(mask) {
  install(mask);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0;
  const start=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null});
  }
  return {mask:mask||"none",counts,wrong,totalSteps,elapsed_ms:Date.now()-start,results};
}

const variants=[];
for(const mask of ["","G","V","I","GV","GI","VI","GVI"]) variants.push(evaluate(mask));
proto.run=originalRun; proto.getApp=originalGetApp;
proto.validate=originalValidate; proto.instantiateDeclaration=originalInstantiate;

const baseline=variants[0];
if(baseline.wrong) throw new Error("baseline wrong");
const residualNames=new Set(baseline.results.filter(r=>r.status==="UNKNOWN"&&
  ["budget-exhausted","host-stack-limit"].includes(r.reason)).map(r=>r.name));
if(residualNames.size!==18) throw new Error("baseline residual changed: "+residualNames.size);

const summaries=[];
for(const v of variants) {
  let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
  const resolvedCases=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++) {
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status) {
      protectedChanged++; regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
    }
    if(residualNames.has(r.name)) {
      if(r.status!=="UNKNOWN") {
        if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({mask:v.mask,result:r}));
        resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
        resolvedCases.push({name:r.name,status:r.status,steps:r.steps});
      } else remaining.push({name:r.name,reason:r.reason,steps:r.steps});
    }
  }
  const summary={mask:v.mask,counts:v.counts,wrong:v.wrong,protectedChanged,
    resolved,resolvedAccept,resolvedReject,totalSteps:v.totalSteps,elapsed_ms:v.elapsed_ms,
    resolvedCases,remaining,regressions};
  summaries.push(summary);
  console.log("HOT_OPERATION_CACHE_VARIANT "+JSON.stringify(summary));
}
const lawful=summaries.filter(s=>s.mask!=="none"&&s.wrong===0&&s.protectedChanged===0);
lawful.sort((a,b)=>b.resolved-a.resolved || a.totalSteps-b.totalSteps || a.mask.length-b.mask.length);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],
  lawful_candidates:lawful.map(x=>x.mask),provisional_winner:lawful[0]?.mask??null,
  candidates:summaries.slice(1),
  claim_boundary:"Prospective execution separator. Only completed exact operation results are cached; V is keyed by the complete current universe-parameter list. No semantic equality or Lean rule is added."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/hot-operation-cache-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("HOT_OPERATION_CACHE_CONCLUSION "+JSON.stringify(conclusion));
