// Prospective proof-classification consequence bank.
//
// proofType(e,ctx) is a verified classification used by proof irrelevance:
// it infers e, checks the sort of the inferred type, and returns that type iff
// it is Prop-valued, otherwise null. Repeating that classification can replay
// large inference/sort obligations even when the exact local environment is
// unchanged.
//
// This separator compares:
//   positive: cache only successful "proof of T" classifications;
//   all:      also cache successful "not proof-valued" (null) classifications.
//
// Keys preserve exact expression identity, exact binder order, exact ordinary
// binder identity, exact LocalDef type/value identities, universe parameters,
// and LocalDef/ordinary execution state. Throws/UNKNOWN/REJECT are never cached.
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

const py=[
  "import io,tarfile,json,sys",
  "data=sys.stdin.buffer.read();rows=[]",
  "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
  "  for m in a:",
  "    p=m.name.split('/')",
  "    if not m.isfile() or not m.name.endswith('.ndjson') or m.size>2000000: continue",
  "    e='ACCEPT' if 'good' in p else 'REJECT' if 'bad' in p else None",
  "    if e: rows.append({'name':m.name,'expected':e,'input':a.extractfile(m).read().decode('utf-8')})",
  "print(json.dumps(rows))"
].join("\n");
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==188) throw new Error("Arena row count changed");
const focusRows=rows.filter(r=>
  r.name.endsWith("good/perf/fueled-chain.ndjson") ||
  r.name.endsWith("good/perf/shared-subterm.ndjson")
);
if(focusRows.length!==2) throw new Error("focus rows missing");

const proto=K.Kernel.prototype;
const retainedRun=proto.run;
const retainedProofType=proto.proofType;
const stats={queries:0,hitsPositive:0,hitsNull:0,storesPositive:0,storesNull:0,ctxKeys:0,localEntries:0};

function objectId(k,x){
  k.__proofClassIds??=new WeakMap();k.__proofClassNextId??=1;
  if(x===null || (typeof x!=="object"&&typeof x!=="function"))
    return typeof x+":"+String(x);
  let id=k.__proofClassIds.get(x);
  if(id!==undefined) return "o"+id;
  id=k.__proofClassNextId++;k.__proofClassIds.set(x,id);return "o"+id;
}

function ctxKey(k,ctx){
  stats.ctxKeys++;
  const parts=[];
  for(const x of (ctx??[])){
    if(x?.__localDef===true){
      stats.localEntries++;
      parts.push("D:"+objectId(k,x.type)+":"+objectId(k,x.value));
    } else parts.push("T:"+objectId(k,x));
  }
  const ps=[...(k.params??[])].sort().join(",");
  return (k.localDefs?"L|":"N|")+ps+"|"+parts.join(";");
}

function install(mode){
  proto.run=retainedRun;
  proto.proofType=retainedProofType;
  if(mode==="baseline") return;

  proto.run=function(...args){
    this.__proofClassIds=new WeakMap();this.__proofClassNextId=1;
    this.__proofClassCache=new WeakMap();
    return retainedRun.apply(this,args);
  };

  proto.proofType=function(e,ctx=[]){
    if(!Array.isArray(e)) return retainedProofType.call(this,e,ctx);
    stats.queries++;
    this.__proofClassCache??=new WeakMap();
    let byCtx=this.__proofClassCache.get(e);
    if(!byCtx){byCtx=new Map();this.__proofClassCache.set(e,byCtx);}
    const key=ctxKey(this,ctx);
    if(byCtx.has(key)){
      const out=byCtx.get(key);
      if(out===null) stats.hitsNull++; else stats.hitsPositive++;
      return out;
    }
    const out=retainedProofType.call(this,e,ctx);
    if(out!==null){
      byCtx.set(key,out);stats.storesPositive++;
    } else if(mode==="all"){
      byCtx.set(key,null);stats.storesNull++;
    }
    return out;
  };
}

function evaluate(mode,subset,budget){
  install(mode);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null,
      fallback_mode:r.fallback_mode??null,fallback_attempt_reason:r.fallback_attempt_reason??null});
  }
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  return {mode,budget,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results};
}

const focus={
  baseline:evaluate("baseline",focusRows,1_000_000),
  positive:evaluate("positive",focusRows,1_000_000),
  all:evaluate("all",focusRows,1_000_000)
};
for(const x of Object.values(focus)) if(x.wrong) throw new Error("focus wrong verdict");

function score(x){
  const accepted=x.results.filter(r=>r.status==="ACCEPT").length;
  const fueled=x.results.find(r=>r.name.endsWith("fueled-chain.ndjson"));
  return [-accepted,fueled?.status==="ACCEPT"?(fueled.steps??0):1_000_001,x.totalConstructed,x.elapsed_ms];
}
const candidates=[focus.positive,focus.all].sort((a,b)=>{
  const x=score(a),y=score(b);
  for(let i=0;i<x.length;i++) if(x[i]!==y[i]) return x[i]-y[i];
  return a.mode.localeCompare(b.mode);
});
const winnerMode=candidates[0].mode;
let winner=candidates[0];

let cliff=null;
if(!winner.results.some(r=>r.status==="ACCEPT")){
  cliff=evaluate(winnerMode,focusRows,2_000_000);
  if(cliff.wrong) throw new Error("cliff wrong verdict");
  if(cliff.results.some(r=>r.status==="ACCEPT")) winner=cliff;
}

let full=null;
if(winner.results.some(r=>r.status==="ACCEPT")){
  const candidate=evaluate(winnerMode,rows,1_000_000);
  const baseline=evaluate("baseline",rows,1_000_000);
  if(candidate.wrong||baseline.wrong) throw new Error("full wrong verdict");
  let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],c=candidate.results[i];
    if(b.status!=="UNKNOWN"&&c.status!==b.status){
      protectedChanged++;
      regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
    }
    if(b.status==="UNKNOWN"){
      if(c.status!=="UNKNOWN"&&c.status===c.expected)
        resolved.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
      else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,frontier_declaration:c.frontier_declaration});
    }
  }
  full={
    baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
    candidate:{mode:winnerMode,counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
      elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
    lawful:candidate.wrong===0&&protectedChanged===0,
    promotable:candidate.wrong===0&&protectedChanged===0&&resolved.length>0
  };
}
install("baseline");

const report={
  arena_sha256:sha,focus,winner_mode:winnerMode,cliff,full,
  claim_boundary:"Execution consequence reuse only. proofType classification is cached only after retained infer + sort checking returns successfully, under exact expression identity, exact local environment content/order, universe parameters and execution mode. Positive mode caches only proof-valued classifications; all mode additionally caches the verified non-proof-valued null classification. Exceptions and unresolved classifications are never cached."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/prooftype-consequence-bank.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("PROOFTYPE_CONSEQUENCE_BANK "+JSON.stringify(report));
