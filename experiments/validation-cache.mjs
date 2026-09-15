// Separator: compile exact successful validation consequences.
// Validation depends on the exact expression, fixed capabilities, and current
// universe-parameter set. It does not depend on the local term context or env.
// Failures/frontiers are never cached.
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
const originalRun=proto.run, originalValidate=proto.validate;

function paramsKey(kernel){ return [...(kernel.params??[])].sort().join("\u0000"); }
function install(mode){
  proto.run=originalRun; proto.validate=originalValidate;
  if(mode==="baseline") return;
  proto.run=function(...args){
    this.__validationOk=new WeakMap();
    return originalRun.apply(this,args);
  };
  proto.validate=function(e){
    if(!Array.isArray(e)) return originalValidate.call(this,e);
    this.__validationOk??=new WeakMap();
    const key=paramsKey(this);
    let ok=this.__validationOk.get(e);
    if(ok?.has(key)){
      if(mode==="tick") this.tick();
      return;
    }
    // Store only after exact retained validation succeeds.
    const out=originalValidate.call(this,e);
    ok=this.__validationOk.get(e);
    if(!(ok instanceof Set)){ ok=new Set(); this.__validationOk.set(e,ok); }
    ok.add(key);
    return out;
  };
}

const budget=1_000_000;
function evaluate(mode){
  install(mode);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,fallback_mode:r.fallback_mode??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const variants=["baseline","tick","free"].map(evaluate);
proto.run=originalRun; proto.validate=originalValidate;
const baseline=variants[0];
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));

const summaries=[];
for(const v of variants){
  let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
  const resolvedCases=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status){
      protectedChanged++;
      if(regressions.length<20) regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
    }
    if(residual.has(r.name)){
      if(r.status!=="UNKNOWN"){
        if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({mode:v.mode,result:r}));
        resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
        resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
      } else remaining.push({name:r.name,reason:r.reason,steps:r.steps});
    }
  }
  const s={mode:v.mode,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,resolvedAccept,resolvedReject,
    totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,elapsed_ms:v.elapsed_ms,
    resolvedCases,regressions,remaining};
  summaries.push(s); console.log("VALIDATION_CACHE_VARIANT "+JSON.stringify(s));
}
const lawful=summaries.filter(s=>s.mode!=="baseline"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0)
  .sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),
  lawful_candidates:lawful.map(x=>x.mode),provisional_winner:lawful[0]?.mode??null,
  claim_boundary:"Prospective execution compilation only. Cache key is exact term identity plus complete universe-parameter set; capabilities are fixed per Kernel instance; only successful validation is retained."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/validation-cache-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("VALIDATION_CACHE_CONCLUSION "+JSON.stringify(conclusion));
