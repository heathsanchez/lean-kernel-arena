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

const proto=K.Kernel.prototype, retainedEqual=proto.equal;
const stats={eligible:0,aborts:0};

function neutralVarApplication(e){
  if(!Array.isArray(e)||e[0]!=="app") return false;
  let h=e;
  while(Array.isArray(h)&&h[0]==="app") h=h[1];
  return Array.isArray(h)&&h[0]==="var";
}

function install(enabled){
  proto.equal=retainedEqual;
  if(!enabled) return;
  proto.equal=function(a,b,ctx=[]){
    if(!this.localDefs && (this._rigidTypeSpineDepth??0)>0){
      const hit=(Array.isArray(a)&&a[0]==="pi"&&neutralVarApplication(b)) ||
                (Array.isArray(b)&&b[0]==="pi"&&neutralVarApplication(a));
      if(hit){
        stats.eligible++;
        stats.aborts++;
        this.unknown("rigid-spine-neutral-pi-obstruction");
      }
    }
    return retainedEqual.call(this,a,b,ctx);
  };
}

function evaluate(mode,enabled,subset=rows){
  install(enabled);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0; const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]++; totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
      fallback_mode:r.fallback_mode??null,fallback_attempt_reason:r.fallback_attempt_reason??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,
    stats:{eligible:stats.eligible-before.eligible,aborts:stats.aborts-before.aborts},results};
}

const focusRows=rows.filter(r=>r.name.endsWith("good/perf/fueled-chain.ndjson"));
const focusBase=evaluate("focus-baseline",false,focusRows);
const focus=evaluate("focus-candidate",true,focusRows);
console.log("RIGID_SPINE_FAST_ABORT_FOCUS "+JSON.stringify({baseline:focusBase,candidate:focus}));
if(focus.wrong) throw new Error("focus wrong");

const baseline=evaluate("baseline",false);
const candidate=evaluate("candidate",true);
install(false);
if(baseline.wrong||candidate.wrong) throw new Error("wrong verdict");

let protectedChanged=0; const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++; regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"){
    if(c.status!=="UNKNOWN"&&c.status===c.expected) resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
    else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,frontier_declaration:c.frontier_declaration});
  }
}
const report={arena_sha256:sha,budget:1_000_000,
 baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
   elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved.some(r=>r.name.endsWith("fueled-chain.ndjson")),
 claim_boundary:"Execution routing only. While an already-bounded rigid type-spine congruence transaction is active in the ordinary kernel, a raw Pi versus an application with neutral local-variable head aborts that speculation as UNKNOWN. The rigid-spine layer restores the transaction and delegates to its retained fallback. No ACCEPT or REJECT consequence is introduced."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/rigid-spine-fast-abort.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("RIGID_SPINE_FAST_ABORT "+JSON.stringify(report));
