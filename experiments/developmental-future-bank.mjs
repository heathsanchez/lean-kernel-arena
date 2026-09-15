import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const arenaSha=createHash("sha256").update(data).digest("hex");
if(arenaSha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    p="/".join(m.name.split("/")[-3:])
    parts=m.name.split("/")
    expected="ACCEPT" if "good" in parts else "REJECT" if "bad" in parts else None
    if expected:
      rows.append({"name":p,"expected":expected,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(sorted(rows,key=lambda x:x["name"])))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==188) throw new Error("expected 188 Arena rows, got "+rows.length);

function mechanism(name){
  if(name.includes("magma-list")) return "magma";
  if(/beta-ladder|let-ladder|shift-cascade|church-numerals|shared-subterm/.test(name)) return "substitution";
  if(/app-lam|repeated-subproblem/.test(name)) return "sharing";
  if(/folded-constant|fueled-chain|args-before-unfold|unroll-versus-evaluate|irrelevance-before-evaluation/.test(name)) return "unfolding";
  if(name.includes("refute-cheap")) return "refutation";
  return "core";
}

const proto=K.Kernel.prototype;
const baseRun=proto.run, baseProofType=proto.proofType, baseGetApp=proto.getApp, baseSame=proto.same;

function objectId(k,x){
  k.__dfbIds??=new WeakMap(); k.__dfbNextId??=1;
  let id=k.__dfbIds.get(x);
  if(id!==undefined) return id;
  id=k.__dfbNextId++; k.__dfbIds.set(x,id); return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length) return "";
  return ctx.map(x=>(x!==null&&(typeof x==="object"||typeof x==="function"))
    ?"o"+objectId(k,x):typeof x+":"+String(x)).join(",");
}
function paramsKey(k){ return [...(k.params??[])].sort().join("\u0000"); }

function install(mode){
  proto.run=baseRun; proto.proofType=baseProofType; proto.getApp=baseGetApp; proto.same=baseSame; proto.same=baseSame;
  if(mode==="baseline") return;
  const useProof=mode==="proof"||mode==="both";
  const useGetApp=mode==="getapp"||mode==="both";
  proto.run=function(...args){
    this.__dfbProof=new WeakMap();
    this.__dfbGetApp=new WeakMap();
    this.__dfbIds=new WeakMap();
    this.__dfbNextId=1;
    return baseRun.apply(this,args);
  };
  if(useProof){
    proto.proofType=function(e,ctx=[]){
      if(!Array.isArray(e)) return baseProofType.call(this,e,ctx);
      this.__dfbProof??=new WeakMap();
      let byKey=this.__dfbProof.get(e);
      if(!byKey){byKey=new Map();this.__dfbProof.set(e,byKey);}
      const key=paramsKey(this)+"|"+ctxKey(this,ctx);
      if(byKey.has(key)) return byKey.get(key);
      const out=baseProofType.call(this,e,ctx);
      byKey.set(key,out);
      return out;
    };
  }
  if(useGetApp){
    proto.getApp=function(e){
      if(!Array.isArray(e)) return baseGetApp.call(this,e);
      this.__dfbGetApp??=new WeakMap();
      if(this.__dfbGetApp.has(e)) return this.__dfbGetApp.get(e);
      const out=baseGetApp.call(this,e);
      this.__dfbGetApp.set(e,out);
      return out;
    };
  }
}

function runMode(mode){
  install(mode);
  const results=[];
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    const wrong=r.status!=="UNKNOWN"&&r.status!==row.expected;
    results.push({
      name:row.name,expected:row.expected,group:mechanism(row.name),
      status:r.status,reason:r.reason??null,steps:r.steps??null,
      constructed:r.constructed??null,wrong
    });
  }
  return {mode,elapsed_ms:Date.now()-t0,results};
}

const modes=["baseline","proof","getapp","same","both","getapp-same","proof-same","all"];
const runs=Object.fromEntries(modes.map(mode=>[mode,runMode(mode)]));
proto.run=baseRun; proto.proofType=baseProofType; proto.getApp=baseGetApp;

const baselineByName=new Map(runs.baseline.results.map(r=>[r.name,r]));
function metrics(results,names){
  const chosen=names?results.filter(r=>names.has(r.name)):results;
  return {
    total:chosen.length,
    accept:chosen.filter(r=>r.status==="ACCEPT").length,
    reject:chosen.filter(r=>r.status==="REJECT").length,
    unknown:chosen.filter(r=>r.status==="UNKNOWN").length,
    wrong:chosen.filter(r=>r.wrong).length,
    steps:chosen.reduce((s,r)=>s+(r.steps??0),0),
    constructed:chosen.reduce((s,r)=>s+(r.constructed??0),0)
  };
}
function changedProtected(results,names){
  let n=0;
  for(const r of results){
    if(names&&!names.has(r.name)) continue;
    const b=baselineByName.get(r.name);
    if(b.status!=="UNKNOWN" && r.status!==b.status) n++;
  }
  return n;
}
function strictlyBetter(candidate,base){
  if(candidate.unknown<base.unknown) return true;
  if(candidate.unknown>base.unknown) return false;
  if(candidate.steps < base.steps*0.99) return true;
  if(candidate.steps > base.steps) return false;
  return candidate.constructed < base.constructed*0.99;
}
function rank(m){ return [m.unknown,m.steps,m.constructed]; }
function less(a,b){
  for(let i=0;i<a.length;i++){ if(a[i]!==b[i]) return a[i]<b[i]; }
  return false;
}

const groups=[...new Set(rows.map(r=>mechanism(r.name)))].sort();
const worlds=[];
for(const heldout of groups){
  const futureNames=new Set(rows.filter(r=>mechanism(r.name)===heldout).map(r=>r.name));
  const discoveryNames=new Set(rows.filter(r=>mechanism(r.name)!==heldout).map(r=>r.name));
  const baseDiscovery=metrics(runs.baseline.results,discoveryNames);
  const candidates=[];
  for(const mode of modes.slice(1)){
    const rm=metrics(runs[mode].results,discoveryNames);
    const protectedChanged=changedProtected(runs[mode].results,discoveryNames);
    const safe=rm.wrong===0&&protectedChanged===0;
    if(safe&&strictlyBetter(rm,baseDiscovery)) candidates.push({mode,metrics:rm,protectedChanged});
  }
  candidates.sort((a,b)=>less(rank(a.metrics),rank(b.metrics))?-1:less(rank(b.metrics),rank(a.metrics))?1:a.mode.localeCompare(b.mode));
  const selected=candidates[0]??null;
  if(!selected){
    worlds.push({future:heldout,compiled:false,selected:null,future_search_calls:0,accepted:false,revoked:false,
      discovery:{baseline:baseDiscovery,candidates:[]}});
    continue;
  }
  const baseFuture=metrics(runs.baseline.results,futureNames);
  const candFuture=metrics(runs[selected.mode].results,futureNames);
  const futureProtectedChanged=changedProtected(runs[selected.mode].results,futureNames);
  const safeFuture=candFuture.wrong===0&&futureProtectedChanged===0;
  const accepted=safeFuture&&strictlyBetter(candFuture,baseFuture);
  worlds.push({
    future:heldout,compiled:true,selected:selected.mode,future_search_calls:0,
    accepted,revoked:!accepted,
    discovery:{baseline:baseDiscovery,selected:selected.metrics,protectedChanged:selected.protectedChanged},
    future_metrics:{baseline:baseFuture,candidate:candFuture,protectedChanged:futureProtectedChanged}
  });
}

const modeSummary={};
for(const mode of modes){
  const m=metrics(runs[mode].results);
  modeSummary[mode]={...m,protectedChanged:mode==="baseline"?0:changedProtected(runs[mode].results),elapsed_ms:runs[mode].elapsed_ms,
    resolved: mode==="baseline"?[]:runs[mode].results.filter(r=>baselineByName.get(r.name).status==="UNKNOWN"&&r.status!=="UNKNOWN"&&!r.wrong).map(r=>r.name),
    regressions: mode==="baseline"?[]:runs[mode].results.filter(r=>baselineByName.get(r.name).status!=="UNKNOWN"&&r.status!==baselineByName.get(r.name).status).map(r=>r.name)
  };
}

const report={
  arena_sha256:arenaSha,
  invariant:"candidate policies compile exact completed consequences only; unsupported states fall back to retained kernel",
  groups,
  modes:modeSummary,
  worlds,
  totals:{
    future_worlds:worlds.length,
    compiled_memories:worlds.filter(w=>w.compiled).length,
    accepted_memories:worlds.filter(w=>w.accepted).length,
    revoked_memories:worlds.filter(w=>w.revoked).length,
    refused_memories:worlds.filter(w=>!w.compiled).length,
    future_search_calls:worlds.reduce((s,w)=>s+w.future_search_calls,0)
  }
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/developmental-future-bank.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("DEVELOPMENTAL_FUTURE_BANK "+JSON.stringify(report));
