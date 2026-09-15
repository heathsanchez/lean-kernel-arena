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
const retainedWhnf=proto.whnf;
const stats={queries:0,hits:0,stores:0};

function objectId(k,x){
  k.__whnfCtxIds??=new WeakMap();
  k.__whnfNextCtxId??=1;
  let id=k.__whnfCtxIds.get(x);
  if(id!==undefined) return id;
  id=k.__whnfNextCtxId++;
  k.__whnfCtxIds.set(x,id);
  return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length) return "";
  return ctx.map(x=>(x!==null&&(typeof x==="object"||typeof x==="function"))
    ?"o"+objectId(k,x):typeof x+":"+String(x)).join(",");
}
function resetCandidate(){
  proto.run=retainedRun;
  proto.whnf=retainedWhnf;
}
function installCandidate(){
  resetCandidate();
  proto.run=function(...args){
    this.__whnfConsequence=new WeakMap();
    this.__whnfCtxIds=new WeakMap();
    this.__whnfNextCtxId=1;
    return retainedRun.apply(this,args);
  };
  proto.whnf=function(e){
    stats.queries++;
    if(!Array.isArray(e)) return retainedWhnf.call(this,e);
    this.__whnfConsequence??=new WeakMap();
    const ckey=this.localDefs ? ctxKey(this,this._activeCtx??[]) : "";
    let slot=this.__whnfConsequence.get(e);
    if(this.localDefs){
      if(!(slot instanceof Map)){slot=new Map();this.__whnfConsequence.set(e,slot);}
      if(slot.has(ckey)){stats.hits++;return slot.get(ckey);}
      const out=retainedWhnf.call(this,e);
      slot.set(ckey,out); stats.stores++; return out;
    }
    if(slot!==undefined){stats.hits++;return slot;}
    const out=retainedWhnf.call(this,e);
    this.__whnfConsequence.set(e,out); stats.stores++; return out;
  };
}
function evaluate(mode){
  mode==="candidate"?installCandidate():resetCandidate();
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
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,
    stats:{queries:stats.queries-before.queries,hits:stats.hits-before.hits,stores:stats.stores-before.stores},results};
}
const baseline=evaluate("baseline");
const candidate=evaluate("candidate");
resetCandidate();
if(baseline.wrong||candidate.wrong) throw new Error("wrong verdict in separator");

let protectedChanged=0;
const resolved=[],regressions=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++; regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"&&c.status!=="UNKNOWN"){
    if(c.status!==c.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(c));
    resolved.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
  }
}
const summary={
  arena_sha256:sha,budget:1_000_000,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
    elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved.length>0,
  claim_boundary:"Successful weak-head reduction only. Cache key is exact expression identity and, when LocalDef semantics are active, the complete exact local-context identity signature already retained by normal-form consequence reuse. Failures/frontiers are never cached; kernel rules are unchanged."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/whnf-consequence-separator.json",import.meta.url),JSON.stringify(summary,null,2)+"\n");
console.log("WHNF_CONSEQUENCE_SEPARATOR "+JSON.stringify(summary));
