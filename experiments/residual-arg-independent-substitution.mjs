// Test exact one-pass binder-independent substitution on the current
// substitution-dominated residual frontier.
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
wanted={
"good/perf/magma-list-deep-n21.ndjson",
"good/perf/magma-list-deep-n36.ndjson",
"good/perf/magma-list-pair-n21.ndjson",
"good/perf/magma-list-pair-n7.ndjson",
"good/perf/shared-subterm.ndjson"
}
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and p in wanted:
      rows.append({"name":p,"expected":"ACCEPT","input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const focusRows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(focusRows.length!==5)throw new Error("focus rows missing");

const proto=K.Kernel.prototype;
const retainedRun=proto.run,retainedSubstitute=proto.substitute,retainedLowerBound=proto.lowerBound;
const stats={queries:0,hitsUnused:0,hitsUsed:0,storesUnused:0,storesUsed:0,probeFailures:0};

function slot(k,e,depth){
  k.__residualArgIndependent??=new WeakMap();
  let m=k.__residualArgIndependent.get(e);
  if(!m){m=new Map();k.__residualArgIndependent.set(e,m);}
  return {m,depth};
}
function install(enabled){
  proto.run=retainedRun;proto.substitute=retainedSubstitute;
  if(!enabled)return;
  proto.run=function(...args){
    this.__residualArgIndependent=new WeakMap();
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
function evalRows(mode,enabled,rows){
  install(enabled);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null});
  }
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results};
}
const baseline=evalRows("baseline",false,focusRows),candidate=evalRows("candidate",true,focusRows);
install(false);
console.log("RESIDUAL_ARG_INDEPENDENT_FOCUS "+JSON.stringify({baseline,candidate}));
if(candidate.wrong)throw new Error("focus wrong");
if(!candidate.results.some(r=>r.status==="ACCEPT")){
  console.log("RESIDUAL_ARG_INDEPENDENT_STOP "+JSON.stringify({reason:"no-focus-resolution",baseline,candidate}));
  process.exit(0);
}

const pyAll=String.raw`
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
const rows=JSON.parse(execFileSync("python3",["-c",pyAll],{input:data,maxBuffer:50000000,timeout:10000}));
const cand=evalRows("candidate-full",true,rows),base=evalRows("baseline-full",false,rows);install(false);
if(cand.wrong||base.wrong)throw new Error("wrong verdict");
let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=base.results[i],c=cand.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});}
  if(b.status==="UNKNOWN"){
    if(c.status!=="UNKNOWN"&&c.status===rows[i].expected)resolved.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
    else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
  }
}
const report={arena_sha256:sha,budget:1000000,focus:{baseline,candidate},
 baseline:{counts:base.counts,totalSteps:base.totalSteps,totalConstructed:base.totalConstructed,elapsed_ms:base.elapsed_ms},
 candidate:{counts:cand.counts,totalSteps:cand.totalSteps,totalConstructed:cand.totalConstructed,elapsed_ms:cand.elapsed_ms,
   stats:cand.stats,protectedChanged,resolved,regressions,remaining},
 lawful:cand.wrong===0&&protectedChanged===0,
 promotable:cand.wrong===0&&protectedChanged===0&&resolved.length>0,
 claim_boundary:"Exact one-pass binder-independence compilation only. A successful lowerBound(body,depth) proves the target binder absent and constructs the exact lowered result, cached by immutable body identity + depth. Null/failed probes delegate to retained argument-sensitive substitution."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/residual-arg-independent-substitution.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("RESIDUAL_ARG_INDEPENDENT "+JSON.stringify(report));
