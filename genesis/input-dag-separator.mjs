// Prospective separator: exact canonicalization of parsed array structure.
// This changes representation only: structurally identical immutable arrays become
// one object before the retained identity-exact transform caches see them.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "./kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("./evidence/retained.json",import.meta.url),"utf8"));
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
const originalRun=proto.run;

function install(enabled) {
  proto.run=originalRun;
  if(!enabled) return;
  proto.run=function(term,expected,declarations=[],parameters=[]) {
    const cons=new Map(), ids=new WeakMap(), seen=new WeakMap();
    let nextId=1, arraysSeen=0;
    const oid=x=>{
      let id=ids.get(x);
      if(id===undefined){ id=nextId++; ids.set(x,id); }
      return id;
    };
    const scalar=x=>{
      if(x===null) return "null";
      const t=typeof x;
      return t+":"+JSON.stringify(x);
    };
    const canon=v=>{
      if(Array.isArray(v)) {
        const prior=seen.get(v); if(prior!==undefined) return prior;
        arraysSeen++;
        const xs=v.map(canon);
        const key=xs.map(x=>Array.isArray(x)?"a:"+oid(x):x&&typeof x==="object"?"o:"+oid(x):scalar(x)).join("|");
        let out=cons.get(key);
        if(out===undefined) {
          out=xs.every((x,i)=>x===v[i])?v:xs;
          cons.set(key,out); oid(out);
        }
        seen.set(v,out);
        return out;
      }
      if(v&&typeof v==="object") {
        const prior=seen.get(v); if(prior!==undefined) return prior;
        const out={}; seen.set(v,out); oid(out);
        for(const [k,x] of Object.entries(v)) out[k]=canon(x);
        return out;
      }
      return v;
    };
    const t=canon(term), e=canon(expected), ds=declarations.map(canon);
    const r=originalRun.call(this,t,e,ds,parameters);
    r.input_arrays_seen=arraysSeen;
    r.input_arrays_unique=cons.size;
    return r;
  };
}

const budget=1_000_000;
function evaluate(name,enabled) {
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalSeen=0,totalUnique=0;
  const start=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;
    totalSeen+=r.input_arrays_seen??0; totalUnique+=r.input_arrays_unique??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null,
      input_arrays_seen:r.input_arrays_seen??null,input_arrays_unique:r.input_arrays_unique??null});
  }
  return {name,counts,wrong,totalSteps,elapsed_ms:Date.now()-start,totalSeen,totalUnique,results};
}

const baseline=evaluate("baseline",false);
if(baseline.wrong) throw new Error("baseline wrong");
const residualNames=new Set(baseline.results.filter(r=>r.status==="UNKNOWN"&&
  ["budget-exhausted","host-stack-limit"].includes(r.reason)).map(r=>r.name));
if(residualNames.size!==18) throw new Error("baseline residual changed: "+residualNames.size);

const candidate=evaluate("input-dag",true);
proto.run=originalRun;

let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],residualDeltas=[];
for(let i=0;i<rows.length;i++) {
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status) {
    protectedChanged++; regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residualNames.has(r.name)) {
    residualDeltas.push({name:r.name,before:b.status,after:r.status,reason:r.reason,
      beforeSteps:b.steps,afterSteps:r.steps,
      deltaSteps:(b.steps??0)-(r.steps??0),
      inputArrays:r.input_arrays_seen,uniqueArrays:r.input_arrays_unique});
    if(r.status!=="UNKNOWN") {
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
      resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,steps:r.steps});
    }
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,
    totalInputArrays:candidate.totalSeen,totalUniqueArrays:candidate.totalUnique},
  lawful:candidate.wrong===0&&protectedChanged===0,
  residualDeltas:residualDeltas.sort((a,b)=>b.deltaSteps-a.deltaSteps),
  claim_boundary:"Prospective representation repair only. Exact structural array canonicalization; no semantic equality, context state, or Lean rule is added."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/input-dag-separator.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("INPUT_DAG_SEPARATOR "+JSON.stringify(summary));
