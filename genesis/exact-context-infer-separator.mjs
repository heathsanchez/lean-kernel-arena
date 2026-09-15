// Prospective separator: exact inference reuse keyed by the complete immutable
// expression plus the complete current local-context contents. This repairs the
// earlier unsound context-array-identity cache: a later mutation of the same
// JS context array produces a different key.
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
const originalRun=proto.run, originalInfer=proto.infer;

function install(enabled){
  proto.run=originalRun; proto.infer=originalInfer;
  proto.run=function(...args){
    this.__inferMemo=new WeakMap();
    this.__ctxObjectIds=new WeakMap();
    this.__nextCtxObjectId=1;
    return originalRun.apply(this,args);
  };
  if(!enabled) return;
  proto.infer=function(e,ctx){
    if(!Array.isArray(e)||!Array.isArray(ctx)) return originalInfer.call(this,e,ctx);
    let byCtx=this.__inferMemo.get(e);
    if(!byCtx){byCtx=new Map();this.__inferMemo.set(e,byCtx);}
    const ids=[];
    for(const x of ctx){
      if(Array.isArray(x)){
        let id=this.__ctxObjectIds.get(x);
        if(id===undefined){id=this.__nextCtxObjectId++;this.__ctxObjectIds.set(x,id);}
        ids.push("a"+id);
      } else ids.push(typeof x+":"+JSON.stringify(x));
    }
    const key=ids.join("|");
    if(byCtx.has(key)) return byCtx.get(key);
    const out=originalInfer.call(this,e,ctx); // cache successes only
    byCtx.set(key,out);
    return out;
  };
}

const budget=1_000_000;
function evaluate(name,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0}; let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1; totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {name,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}
const baseline=evaluate("baseline",false);
const candidate=evaluate("exact-context-infer",true);
proto.run=originalRun; proto.infer=originalInfer;
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++; regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)){
    if(r.status!=="UNKNOWN"){
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
      resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
    } else remaining.push({name:r.name,reason:r.reason});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,remaining,regressions},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Caches only completed infer(e,ctx) consequences under a key containing the exact identity sequence of every current context type. Reusing a mutated context array cannot collide because its contents are re-keyed on every call."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/exact-context-infer-separator.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("EXACT_CONTEXT_INFER "+JSON.stringify(summary));
