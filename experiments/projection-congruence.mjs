// Prospective separator: congruence for identical projections.
//
// If both terms are projections with the exact same structure name and field
// index, definitional equality of their objects implies equality of the
// projections. This adds no equality law; it exposes a missing congruence case.
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
if(rows.length!==188) throw new Error("Arena row count changed");

const proto=K.Kernel.prototype;
const retainedEqual=proto.equal;
function install(enabled) {
  proto.equal=retainedEqual;
  if(!enabled) return;
  proto.equal=function(a,b,ctx=[]) {
    if(Array.isArray(a)&&Array.isArray(b)&&
       a[0]==="proj"&&b[0]==="proj"&&
       a[1]===b[1]&&a[2]===b[2]) {
      return retainedEqual.call(this,a[3],b[3],ctx);
    }
    return retainedEqual.call(this,a,b,ctx);
  };
}

const budget=1_000_000;
function evaluate(mode,enabled) {
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      frontier:r.conversion_frontier??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false);
const candidate=evaluate("same-projection-congruence",true);
install(false);
if(baseline.wrong) throw new Error("baseline wrong");

const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++) {
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status) {
    protectedChanged++;
    regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)&&r.status!=="UNKNOWN"&&r.status===r.expected) {
    resolved++;
    resolvedCases.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed});
  } else if(residual.has(r.name)) {
    remaining.push({name:r.name,reason:r.reason,steps:r.steps,constructed:r.constructed,
      frontier:r.frontier?{ctx_depth:r.frontier.ctx_depth,left_bytes:r.frontier.left_bytes,right_bytes:r.frontier.right_bytes}:null});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Exact same-projection congruence only: identical structure name and field index; compare the projected objects with the retained converter."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/projection-congruence.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("PROJECTION_CONGRUENCE "+JSON.stringify(summary));
