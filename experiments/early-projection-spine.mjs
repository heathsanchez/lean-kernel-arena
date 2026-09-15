// Prospective early projection-spine congruence.
//
// Before retained conversion normalizes either side, identical projection
// operators may compare the raw application spines of their structure terms.
// If those structures have the exact same raw head and arity, argument-wise
// definitional equality proves structure equality by application congruence,
// hence projection equality. Failure is transactional and delegates unchanged.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");
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
if(rows.length!==188)throw new Error("Arena row count changed");

const proto=K.Kernel.prototype,retained=proto.equal,CAP=75000;
function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {head:h,args};
}
function cheapPair(a,b){
  if(a===b)return -1000000;
  if(!Array.isArray(a)||!Array.isArray(b))return -10000;
  if(a[0]!==b[0])return -100000;
  if(["const","var","nat","strlit","sort"].includes(a[0]))return -50000;
  let score=0,stack=[a,b],seen=new Set();
  while(stack.length&&score<256){
    const x=stack.pop();
    if(!Array.isArray(x)||seen.has(x))continue;
    seen.add(x);score++;
    for(let i=1;i<x.length;i++)if(Array.isArray(x[i]))stack.push(x[i]);
  }
  return score;
}
function install(enabled){
  proto.equal=retained;
  if(!enabled)return;
  proto.equal=function(a,b,ctx=[]){
    if(this.localDefs||(this._earlyProjSpineDepth??0)>0)
      return retained.call(this,a,b,ctx);
    if(this.same(a,b))return;

    if(Array.isArray(a)&&Array.isArray(b)&&
       a[0]==="proj"&&b[0]==="proj"&&a[1]===b[1]&&a[2]===b[2]){
      const sa=rawSpine(a[3]),sb=rawSpine(b[3]);
      const sameHead=sa.args.length>0&&sa.args.length===sb.args.length&&
        (sa.head===sb.head||this.same(sa.head,sb.head));
      if(sameHead){
        const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
        this.budget=Math.min(this.budget,this.steps+CAP);
        this._earlyProjSpineDepth=1;
        const order=sa.args.map((_,i)=>i)
          .sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
        try{
          for(const i of order)retained.call(this,sa.args[i],sb.args[i],ctx);
          this._earlyProjSpineDepth=0;
          this.budget=snap.budget;
          return;
        }catch(e){
          this._earlyProjSpineDepth=0;
          this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
          if(!(e instanceof Stop||e instanceof RangeError))throw e;
        }
      }
    }
    return retained.call(this,a,b,ctx);
  };
}

function evaluate(mode,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const wrongCases=[];
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
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
const baseline=evaluate("baseline",false),candidate=evaluate("early-projection-spine",true);
proto.equal=retained;
if(baseline.wrong)throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){protectedChanged++;regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});}
  if(residual.has(r.name)&&r.status!=="UNKNOWN"&&r.status===r.expected){
    resolved++;resolvedCases.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }else if(residual.has(r.name))remaining.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps});
}
const summary={arena_sha256:sha,budget:1_000_000,speculation_cap:CAP,
 baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,wrong:candidate.wrong,wrongCases:candidate.wrongCases,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
   protectedChanged,resolved,resolvedCases,regressions,remaining},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
 claim_boundary:"Positive congruence consequence only. Before normalization, identical projection operators over exact same-head structure application spines compare arguments cheapest-first. Success proves ordinary application congruence then projection congruence; any failed speculative proof rolls back exactly to retained conversion."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/early-projection-spine.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("EARLY_PROJECTION_SPINE "+JSON.stringify(summary));
