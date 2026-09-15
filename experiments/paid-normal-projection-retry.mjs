// Prospective separator: reuse normal forms already computed by the retained
// converter when an identical projection pair reaches conversion-frontier.
// No second normalization pass. We traverse the already-paid normal forms once
// and delegate only genuine atom mismatches to the retained converter (notably
// proof irrelevance). A failed retry restores the exact original frontier.
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
const retainedEqual=proto.equal, retainedNormal=proto.normal;

function sameData(a,b){
  if(a===b) return true;
  const work=[[a,b]];
  while(work.length){
    const [x,y]=work.pop();
    if(x===y) continue;
    const xa=Array.isArray(x),ya=Array.isArray(y);
    if(xa!==ya) return false;
    if(!xa||x.length!==y.length) return false;
    for(let i=0;i<x.length;i++){
      const p=x[i],q=y[i];
      if(p===q) continue;
      if(Array.isArray(p)&&Array.isArray(q)) work.push([p,q]);
      else return false;
    }
  }
  return true;
}

function comparePaidNormal(kernel,x,y,ctx){
  const work=[{a:x,b:y,ctx}];
  while(work.length){
    const f=work.pop(),u=f.a,v=f.b,c=f.ctx;
    if(u===v) continue;
    kernel.tick();
    if(!Array.isArray(u)||!Array.isArray(v)){
      retainedEqual.call(kernel,u,v,c);
      continue;
    }
    if(u[0]!==v[0]||u.length!==v.length){
      retainedEqual.call(kernel,u,v,c);
      continue;
    }
    switch(u[0]){
      case "var":
      case "nat":
      case "strlit":
        if(u[1]!==v[1]) retainedEqual.call(kernel,u,v,c);
        break;
      case "sort":
        if(!sameData(u[1],v[1])) retainedEqual.call(kernel,u,v,c);
        break;
      case "const":
        if(u[1]!==v[1]||!sameData(u[2]??[],v[2]??[]))
          retainedEqual.call(kernel,u,v,c);
        break;
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
        if(u[1]!==v[1]||u[2]!==v[2]) retainedEqual.call(kernel,u,v,c);
        else work.push({a:u[3],b:v[3],ctx:c});
        break;
      default:
        retainedEqual.call(kernel,u,v,c);
        break;
    }
  }
}

function install(enabled){
  proto.equal=retainedEqual; proto.normal=retainedNormal;
  if(!enabled) return;

  proto.normal=function(e){
    this.__paidNormals ??= new WeakMap();
    const out=retainedNormal.call(this,e);
    if(Array.isArray(e)) this.__paidNormals.set(e,out);
    return out;
  };

  proto.equal=function(a,b,ctx=[]){
    const frontierBefore=this.conversionFrontier;
    try{
      return retainedEqual.call(this,a,b,ctx);
    }catch(err){
      if(err?.message!=="conversion-frontier" ||
         !Array.isArray(a)||!Array.isArray(b) ||
         a[0]!=="proj"||b[0]!=="proj"||a[1]!==b[1]||a[2]!==b[2])
        throw err;
      const x=this.__paidNormals?.get(a),y=this.__paidNormals?.get(b);
      if(!x||!y) throw err;

      const retrySteps=this.steps,retryBudget=this.budget,retryFrontier=this.conversionFrontier;
      try{
        comparePaidNormal(this,x,y,ctx);
        this.conversionFrontier=frontierBefore;
        return;
      }catch(_retry){
        this.steps=retrySteps;
        this.budget=retryBudget;
        this.conversionFrontier=retryFrontier;
        throw err;
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
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false);
const candidate=evaluate("paid-normal-projection-proof-retry",true);
install(false);
if(baseline.wrong) throw new Error("baseline wrong");

const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++;
    regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)&&r.status!=="UNKNOWN"&&r.status===r.expected){
    resolved++;
    resolvedCases.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }else if(residual.has(r.name)){
    remaining.push({name:r.name,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Only after the retained converter itself reaches conversion-frontier on the same projection name/index. Reuses the exact normal forms already computed in that failed comparison; traverses them once and delegates only genuine atom mismatches to retained conversion. Failed retries restore the original frontier."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/paid-normal-projection-retry.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("PAID_NORMAL_PROJECTION_RETRY "+JSON.stringify(summary));
