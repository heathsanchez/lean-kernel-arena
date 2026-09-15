import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
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
if(rows.length!==188) throw new Error("Arena row count changed");

const proto=K.Kernel.prototype, originalRun=proto.run, originalWhnf=proto.whnf;
function install(mode){
  proto.run=originalRun; proto.whnf=originalWhnf;
  if(mode==="baseline") return;
  proto.run=function(...args){ this.__whnfOk=new WeakMap(); return originalRun.apply(this,args); };
  proto.whnf=function(e){
    if(this.localDefs || !Array.isArray(e)) return originalWhnf.call(this,e);
    this.__whnfOk??=new WeakMap();
    if(this.__whnfOk.has(e)){
      if(mode==="tick") this.tick();
      return this.__whnfOk.get(e);
    }
    const out=originalWhnf.call(this,e);
    this.__whnfOk.set(e,out);
    return out;
  };
}

const budget=1_000_000;
function evaluate(mode){
  install(mode);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0}; let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1; totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,fallback_mode:r.fallback_mode??null,retained_reason:r.retained_reason??null,
      stack_attempt_reason:r.stack_attempt_reason??null,stack_attempt_steps:r.stack_attempt_steps??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}
const variants=["baseline","tick","free"].map(evaluate);
proto.run=originalRun; proto.whnf=originalWhnf;
const baseline=variants[0];
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
const summaries=[];
for(const v of variants){
  let protectedChanged=0,resolved=0; const resolvedCases=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status){ protectedChanged++; regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason}); }
    if(residual.has(r.name)){
      if(r.status!=="UNKNOWN"){
        if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({mode:v.mode,r}));
        resolved++; resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
      } else remaining.push({name:r.name,reason:r.reason,steps:r.steps,stack_attempt_reason:r.stack_attempt_reason,stack_attempt_steps:r.stack_attempt_steps});
    }
  }
  const x={mode:v.mode,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,
    elapsed_ms:v.elapsed_ms,resolvedCases,regressions,remaining};
  summaries.push(x); console.log("WHNF_CACHE_VARIANT "+JSON.stringify(x));
}
const lawful=summaries.filter(x=>x.mode!=="baseline"&&x.wrong===0&&x.protectedChanged===0&&x.resolved>0)
  .sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),
  lawful_candidates:lawful.map(x=>x.mode),provisional_winner:lawful[0]?.mode??null,
  claim_boundary:"Prospective execution compilation only. Successful ordinary-kernel WHNF is cached by exact expression identity for one fixed run. Local-definition reduction is excluded."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/whnf-cache-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("WHNF_CACHE_CONCLUSION "+JSON.stringify(conclusion));
