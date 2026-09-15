// Exact argument-independent substitution consequence.
//
// If lowerBound(body, depth) succeeds, it simultaneously proves that the bound
// variable at 'depth' is absent and constructs exactly the de-Bruijn-lowered
// result of substituting any argument there. Cache that completed consequence by
// immutable body identity + exact depth. If lowerBound returns null (binder used)
// or cannot complete, delegate to the retained substitute path unchanged.
//
// This differs from the earlier unused-argument separator by doing one traversal,
// not occurrence-analysis followed by a second drop traversal.
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
const retainedRun=proto.run,retainedSubstitute=proto.substitute,retainedLowerBound=proto.lowerBound;
const stats={queries:0,hitsUnused:0,hitsUsed:0,storesUnused:0,storesUsed:0,probeFailures:0};

function slot(k,e,depth){
  k.__argIndependent??=new WeakMap();
  let m=k.__argIndependent.get(e);
  if(!m){m=new Map();k.__argIndependent.set(e,m);}
  return {m,depth};
}
function install(enabled){
  proto.run=retainedRun;proto.substitute=retainedSubstitute;
  if(!enabled)return;
  proto.run=function(...args){
    this.__argIndependent=new WeakMap();
    return retainedRun.apply(this,args);
  };
  proto.substitute=function(e,arg,depth=0){
    if(!Array.isArray(e))return retainedSubstitute.call(this,e,arg,depth);
    stats.queries++;
    const {m}=slot(this,e,depth);
    if(m.has(depth)){
      const v=m.get(depth);
      if(v.used){stats.hitsUsed++;return retainedSubstitute.call(this,e,arg,depth);}
      stats.hitsUnused++;return v.out;
    }
    try{
      const out=retainedLowerBound.call(this,e,depth);
      if(out!==null){
        m.set(depth,{used:false,out});stats.storesUnused++;return out;
      }
      m.set(depth,{used:true});stats.storesUsed++;
      return retainedSubstitute.call(this,e,arg,depth);
    }catch(err){
      if(!(err instanceof Stop||err instanceof RangeError))throw err;
      stats.probeFailures++;
      return retainedSubstitute.call(this,e,arg,depth);
    }
  };
}
function evalRows(mode,enabled,subset){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const before={...stats},t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null});
  }
  const delta={};for(const k of Object.keys(before))delta[k]=stats[k]-before[k];
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:delta,results};
}
const focusRows=rows.filter(r=>r.name.endsWith("good/perf/beta-ladder.ndjson"));
const focus=evalRows("focus",true,focusRows);
console.log("ARG_INDEPENDENT_SUBST_FOCUS "+JSON.stringify({focus}));
if(focus.wrong)throw new Error("focus wrong");
if(focus.results[0]?.status!=="ACCEPT"){
  install(false);
  console.log("ARG_INDEPENDENT_SUBST_STOP "+JSON.stringify({reason:"beta-not-closed",focus}));
  process.exit(0);
}

const candidate=evalRows("candidate",true,rows);
const baseline=evalRows("baseline",false,rows);
install(false);
if(candidate.wrong||baseline.wrong)throw new Error("wrong verdict");

let protectedChanged=0;
const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"&&c.status!=="UNKNOWN"&&c.status===c.expected)
    resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
  else if(b.status==="UNKNOWN")
    remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
}
const summary={arena_sha256:sha,budget:1_000_000,focus,
 baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
   elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved.some(r=>r.name.endsWith("beta-ladder.ndjson")),
 claim_boundary:"Exact one-pass binder-independence compilation only. A successful lowerBound(body,depth) both proves the target binder absent and constructs the exact argument-independent substitution result, cached by body identity + depth. Null or failed probes delegate to the retained argument-sensitive substitution."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/argument-independent-substitution.json",import.meta.url),JSON.stringify(summary,null,2)+"\n");
console.log("ARG_INDEPENDENT_SUBST "+JSON.stringify(summary));
