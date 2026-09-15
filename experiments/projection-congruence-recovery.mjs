// Prospective positive conversion consequence: projection congruence recovery.
//
// The retained converter already normalizes both sides. If it gives up at a
// conversion frontier whose normalized forms are the same projection operator,
// compare the normalized structure arguments. Equality of those arguments is a
// sufficient proof that the projections are equal. Failure preserves the
// original UNKNOWN exactly.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop,UNKNOWN} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read();rows=[]
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

const proto=K.Kernel.prototype,retained=proto.equal;
function install(enabled){
  proto.equal=retained;
  if(!enabled)return;
  proto.equal=function(a,b,ctx=[]){
    if(this.localDefs || (this._projectionRecoveryDepth??0)>0)
      return retained.call(this,a,b,ctx);

    try{
      return retained.call(this,a,b,ctx);
    }catch(e){
      if(!(e instanceof Stop) || e.status!==UNKNOWN || e.message!=="conversion-frontier")
        throw e;

      const original=e,frontier=this.conversionFrontier;
      const snap={steps:this.steps,budget:this.budget,frontier};

      // normal-cache should make this nearly free when retained.equal just
      // produced the frontier. We only authorize the shortcut for the exact
      // same projection function.
      let x,y;
      try{
        x=this.normal(a);y=this.normal(b);
      }catch(_){
        this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
        throw original;
      }
      if(!Array.isArray(x)||!Array.isArray(y)||
         x[0]!=="proj"||y[0]!=="proj"||x[1]!==y[1]||x[2]!==y[2]){
        this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
        throw original;
      }

      this._projectionRecoveryDepth=1;
      try{
        this.equal(x[3],y[3],ctx);
        this._projectionRecoveryDepth=0;
        return;
      }catch(_){
        this._projectionRecoveryDepth=0;
        this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
        throw original;
      }
    }
  };
}

const budget=1_000_000;
function evaluate(mode,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const wrongCases=[];
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected){
      wrong++;wrongCases.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null});
    }
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode,counts,wrong,wrongCases,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false),candidate=evaluate("projection-congruence-recovery",true);
proto.equal=retained;
if(baseline.wrong)throw new Error("baseline wrong");

const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++;regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)&&r.status!=="UNKNOWN"&&r.status===r.expected){
    resolved++;resolvedCases.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }else if(residual.has(r.name)){
    remaining.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,wrongCases:candidate.wrongCases,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Positive congruence consequence only. After retained conversion returns UNKNOWN at a frontier, identical normalized projection operators may compare their normalized structure arguments. Success proves projection equality; any failure restores and rethrows the original UNKNOWN."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/projection-congruence-recovery.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("PROJECTION_CONGRUENCE_RECOVERY "+JSON.stringify(summary));
