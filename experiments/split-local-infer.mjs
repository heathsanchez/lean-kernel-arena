// Separator: keep the new continuation-machine inference for ordinary checking,
// but preserve the previously verified stack-safe spine inference inside the
// local-definition fallback. This tests the exact shift-cascade regression.
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
const continuationInfer=proto.infer;

function install(enabled){
  proto.infer=continuationInfer;
  if(!enabled) return;
  proto.infer=function(e,ctx){
    if(!this.localDefs) return continuationInfer.call(this,e,ctx);

    // This is the exact pre-continuation stack-safe spine strategy that had
    // already discharged shift-cascade through the local-definition fallback.
    if(Array.isArray(e) && e[0]==="app"){
      const args=[]; let head=e;
      while(Array.isArray(head) && head[0]==="app"){
        this.tick(); this.need("application");
        args.push(head[2]); head=head[1];
      }
      args.reverse();
      let ty=this.infer(head,ctx);
      for(const arg of args){
        const f=this.whnf(ty);
        if(f[0]!=="pi") this.reject("not-a-function");
        this.equal(this.infer(arg,ctx),f[1],ctx);
        ty=this.substitute(f[2],arg);
      }
      return ty;
    }

    if(Array.isArray(e) && e[0]==="lam"){
      const domains=[]; let cur=e,cctx=ctx;
      while(Array.isArray(cur) && cur[0]==="lam"){
        this.tick(); this.need("binders");
        this.sortOf(cur[1],cctx);
        domains.push(cur[1]);
        cctx=[...cctx,cur[1]];
        cur=cur[2];
      }
      let ty=this.infer(cur,cctx);
      for(let i=domains.length-1;i>=0;i--) ty=this.make("pi",domains[i],ty);
      return ty;
    }

    if(Array.isArray(e) && e[0]==="pi"){
      const levels=[]; let cur=e,cctx=ctx;
      while(Array.isArray(cur) && cur[0]==="pi"){
        this.tick(); this.need("binders");
        const a=this.sortOf(cur[1],cctx);
        levels.push(a);
        cctx=[...cctx,cur[1]];
        cur=cur[2];
      }
      let b=this.sortOf(cur,cctx),out=null;
      for(let i=levels.length-1;i>=0;i--){
        const a=levels[i];
        const u=(typeof a==="number"&&typeof b==="number") ? (b===0?0:Math.max(a,b)) : ["imax",a,b];
        out=this.make("sort",u);
        if(i>0) b=this.whnf(out)[1];
      }
      return out;
    }

    // LocalDefKernel itself handles let/var before calling super.infer.
    return continuationInfer.call(this,e,ctx);
  };
}

const budget=1_000_000;
function evaluate(name,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      fallback_mode:r.fallback_mode??null,retained_reason:r.retained_reason??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null,
      diagnostic_error:r.diagnostic_error??null});
  }
  return {name,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false);
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
const candidate=evaluate("split-local-infer",true);
proto.infer=continuationInfer;

let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++;
    regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)){
    if(r.status!=="UNKNOWN"){
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
      resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
    } else remaining.push({name:r.name,reason:r.reason,steps:r.steps,diagnostic_error:r.diagnostic_error});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  claim_boundary:"Prospective execution routing only. Ordinary inference keeps the continuation machine; the local-definition fallback reuses its previously verified stack-safe spine inference. No typing or conversion rule changes."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/split-local-infer.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("SPLIT_LOCAL_INFER "+JSON.stringify(summary));
