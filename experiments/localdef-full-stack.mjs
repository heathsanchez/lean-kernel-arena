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
if(rows.length!==188) throw new Error("Arena row count changed: "+rows.length);

const proto=K.Kernel.prototype, originalRun=proto.run;
function install(enabled){
  proto.run=originalRun;
  if(!enabled) return;
  proto.run=function(...args){
    const had=Object.prototype.hasOwnProperty.call(this,"_fullStackSafe");
    const old=this._fullStackSafe;
    if(this.localDefs===true) this._fullStackSafe=true;
    try{return originalRun.apply(this,args);}
    finally{
      if(this.localDefs===true){
        if(had)this._fullStackSafe=old;
        else delete this._fullStackSafe;
      }
    }
  };
}
const budget=1_000_000;
function evaluate(mode,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      fallback_mode:r.fallback_mode??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}
const baseline=evaluate("baseline",false),candidate=evaluate("local-full-stack",true);
proto.run=originalRun;
if(baseline.wrong||candidate.wrong)throw new Error("wrong verdict");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){protectedChanged++;regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});}
  if(residual.has(r.name)){
    if(r.status!=="UNKNOWN"){
      if(r.status!==r.expected)throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
      resolved++;resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
    } else remaining.push({name:r.name,reason:r.reason,steps:r.steps,fallback_attempt_reason:r.fallback_attempt_reason??null});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms},
  protectedChanged,resolved,resolvedCases,regressions,remaining,
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Execution-only separator. Enables the already-retained full continuation/work-stack evaluator solely inside the LocalDefKernel fallback; no typing, reduction, conversion, or declaration rule changes."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/localdef-full-stack.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("LOCALDEF_FULL_STACK "+JSON.stringify(summary));
