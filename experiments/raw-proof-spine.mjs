// Prospective execution-order separator: walk an identical raw projection spine
// before recursively normalizing the whole tree. This adds no equality law.
// A successful fast path uses only existing congruence, WHNF reduction, and
// proof irrelevance; any failed probe restores the resource/frontier state and
// delegates to the retained converter unchanged.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

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
const ABORT=Symbol("raw-proof-spine-abort");

function changed(a,b){ return a!==b; }

function rawProofSpine(kernel,a,b,ctx) {
  const work=[{a,b,ctx}];
  while(work.length) {
    const f=work.pop(),u=f.a,v=f.b,c=f.ctx;
    if(u===v || kernel.same(u,v)) continue;
    if(!Array.isArray(u)||!Array.isArray(v)) throw ABORT;

    if(u[0]!==v[0]) {
      const wu=kernel.whnf(u),wv=kernel.whnf(v);
      if(changed(wu,u)||changed(wv,v)) { work.push({a:wu,b:wv,ctx:c}); continue; }
      throw ABORT;
    }

    switch(u[0]) {
      case "var": {
        if(u[1]===v[1]) break;
        const tu=kernel.proofType(u,c),tv=kernel.proofType(v,c);
        if(tu===null||tv===null) throw ABORT;
        if(!kernel.same(tu,tv)) retainedEqual.call(kernel,tu,tv,c);
        break;
      }
      case "nat":
      case "strlit":
        if(u[1]!==v[1]) throw ABORT;
        break;
      case "sort":
        if(!kernel.same(u,v)) throw ABORT;
        break;
      case "const": {
        if(kernel.same(u,v)) break;
        const wu=kernel.whnf(u),wv=kernel.whnf(v);
        if(changed(wu,u)||changed(wv,v)) { work.push({a:wu,b:wv,ctx:c}); break; }
        throw ABORT;
      }
      case "app":
        work.push({a:u[2],b:v[2],ctx:c});
        work.push({a:u[1],b:v[1],ctx:c});
        break;
      case "pi":
      case "lam":
        work.push({a:u[2],b:v[2],ctx:[...c,u[1]]});
        work.push({a:u[1],b:v[1],ctx:c});
        break;
      case "proj":
        if(u[1]!==v[1]||u[2]!==v[2]) {
          const wu=kernel.whnf(u),wv=kernel.whnf(v);
          if(changed(wu,u)||changed(wv,v)) { work.push({a:wu,b:wv,ctx:c}); break; }
          throw ABORT;
        }
        work.push({a:u[3],b:v[3],ctx:c});
        break;
      default: {
        const wu=kernel.whnf(u),wv=kernel.whnf(v);
        if(changed(wu,u)||changed(wv,v)) { work.push({a:wu,b:wv,ctx:c}); break; }
        throw ABORT;
      }
    }
  }
}

function install(enabled) {
  proto.equal=retainedEqual;
  if(!enabled) return;
  proto.equal=function(a,b,ctx=[]) {
    if(this.localDefs || !this.caps.has("proof-irrelevance") ||
       this._rawProofSpineDepth ||
       !Array.isArray(a)||!Array.isArray(b) ||
       a[0]!=="proj"||b[0]!=="proj"||a[1]!==b[1]||a[2]!==b[2])
      return retainedEqual.call(this,a,b,ctx);

    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    this._rawProofSpineDepth=1;
    try {
      rawProofSpine(this,a,b,ctx);
      return;
    } catch(e) {
      if(e!==ABORT && !(e instanceof Stop) && !(e instanceof RangeError)) throw e;
      this.steps=snap.steps;
      this.budget=snap.budget;
      this.conversionFrontier=snap.frontier;
    } finally {
      this._rawProofSpineDepth=0;
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
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

// Candidate first: avoid granting the candidate a warmed baseline process.
const candidate=evaluate("raw-proof-spine",true);
const baseline=evaluate("baseline",false);
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
    remaining.push({name:r.name,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }
}
const focus=candidate.results.filter(r=>r.name.includes("magma-list-pair-n7")||r.name.includes("magma-list-pair-n21"));
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedCases,regressions,remaining,focus},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolvedCases.some(r=>r.name.includes("magma-list-pair")),
  claim_boundary:"Same raw projection metadata only. Traverse congruent raw constructors lazily; reduce only when the spine stops aligning; discharge differing bound variables only after both independently prove Prop-valued and their proposition types are definitionally equal. Failed probes restore budget/frontier and delegate unchanged."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/raw-proof-spine.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("RAW_PROOF_SPINE "+JSON.stringify(summary));
