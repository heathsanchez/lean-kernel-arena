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
const retainedRun=proto.run;
const retainedInfer=proto.infer;
const stats={app:0,queries:0,hits:0,erasable:0,used:0};

function reset(){proto.run=retainedRun;proto.infer=retainedInfer;}
function install(){
  reset();
  proto.run=function(...args){
    this.__binderErase=new WeakMap();
    return retainedRun.apply(this,args);
  };
  proto.infer=function(e,ctx=[]){
    if(this.localDefs===true || !Array.isArray(e) || e[0]!=="app")
      return retainedInfer.call(this,e,ctx);
    stats.app++;
    this.tick(); this.need("application");
    const f=this.whnf(this.infer(e[1],ctx));
    if(f[0]!=="pi") this.reject("not-a-function");
    this.equal(this.infer(e[2],ctx),f[1],ctx);

    const body=f[2];
    if(!Array.isArray(body)) return this.substitute(body,e[2]);
    stats.queries++;
    this.__binderErase??=new WeakMap();
    let entry=this.__binderErase.get(body);
    if(entry!==undefined){
      stats.hits++;
    } else {
      const lowered=this.lowerBound(body,0);
      entry={lowered};
      this.__binderErase.set(body,entry);
      if(lowered===null) stats.used++; else stats.erasable++;
    }
    return entry.lowered===null ? this.substitute(body,e[2]) : entry.lowered;
  };
}
function evaluate(mode){
  mode==="candidate"?install():reset();
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const before={...stats},t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  const delta=Object.fromEntries(Object.keys(stats).map(k=>[k,stats[k]-before[k]]));
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:delta,results};
}
const baseline=evaluate("baseline"),candidate=evaluate("candidate"); reset();
if(baseline.wrong||candidate.wrong) throw new Error("wrong verdict in separator");

let protectedChanged=0;
const resolved=[],regressions=[],changed=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++; regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"&&c.status!=="UNKNOWN"){
    if(c.status!==c.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(c));
    resolved.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
  }
  if(b.steps!==c.steps||b.constructed!==c.constructed||b.status!==c.status)
    changed.push({name:c.name,before:{status:b.status,steps:b.steps,constructed:b.constructed},
      after:{status:c.status,steps:c.steps,constructed:c.constructed}});
}
changed.sort((a,b)=>(a.after.steps-a.before.steps)-(b.after.steps-b.before.steps));
const summary={arena_sha256:sha,budget:1_000_000,
 baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
   stats:candidate.stats,protectedChanged,resolved,regressions,largestImprovements:changed.slice(0,20)},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved.length>0,
 claim_boundary:"Application-level exact binder erasure. The argument is still inferred and checked against the Pi domain. If lowering the Pi body proves binder 0 absent, that exact lowered body is cached by immutable body identity and reused; otherwise the retained substitution path is unchanged."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/binder-erasure-consequence.json",import.meta.url),JSON.stringify(summary,null,2)+"\n");
console.log("BINDER_ERASURE_CONSEQUENCE "+JSON.stringify(summary));
