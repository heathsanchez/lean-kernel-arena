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
const base={run:proto.run,proofType:proto.proofType,getApp:proto.getApp,same:proto.same,whnf:proto.whnf};
const stats={proof:{q:0,h:0},getapp:{q:0,h:0},same:{q:0,h:0},whnf:{q:0,h:0}};

function objectId(k,x){
  k.__eccIds??=new WeakMap(); k.__eccNextId??=1;
  let id=k.__eccIds.get(x); if(id!==undefined) return id;
  id=k.__eccNextId++; k.__eccIds.set(x,id); return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length) return "";
  return ctx.map(x=>(x!==null&&(typeof x==="object"||typeof x==="function"))
    ?"o"+objectId(k,x):typeof x+":"+String(x)).join(",");
}
function paramsKey(k){return [...(k.params??[])].sort().join("\u0000");}
function reset(){
  proto.run=base.run; proto.proofType=base.proofType; proto.getApp=base.getApp; proto.same=base.same; proto.whnf=base.whnf;
}
function install(){
  reset();
  proto.run=function(...args){
    this.__eccProof=new WeakMap(); this.__eccGetApp=new WeakMap(); this.__eccSame=new WeakMap(); this.__eccWhnf=new WeakMap();
    this.__eccIds=new WeakMap(); this.__eccNextId=1;
    return base.run.apply(this,args);
  };
  proto.proofType=function(e,ctx=[]){
    stats.proof.q++;
    if(!Array.isArray(e)) return base.proofType.call(this,e,ctx);
    let by=this.__eccProof.get(e); if(!by){by=new Map();this.__eccProof.set(e,by);}
    const key=paramsKey(this)+"|"+ctxKey(this,ctx);
    if(by.has(key)){stats.proof.h++;return by.get(key);}
    const out=base.proofType.call(this,e,ctx); by.set(key,out); return out;
  };
  proto.getApp=function(e){
    stats.getapp.q++;
    if(!Array.isArray(e)) return base.getApp.call(this,e);
    if(this.__eccGetApp.has(e)){stats.getapp.h++;return this.__eccGetApp.get(e);}
    const out=base.getApp.call(this,e); this.__eccGetApp.set(e,out); return out;
  };
  proto.same=function(a,b){
    stats.same.q++;
    if(!Array.isArray(a)||!Array.isArray(b)) return base.same.call(this,a,b);
    let by=this.__eccSame.get(a); if(!by){by=new WeakMap();this.__eccSame.set(a,by);}
    if(by.has(b)){stats.same.h++;return by.get(b);}
    const out=base.same.call(this,a,b); by.set(b,out);
    let rev=this.__eccSame.get(b); if(!rev){rev=new WeakMap();this.__eccSame.set(b,rev);} rev.set(a,out);
    return out;
  };
  proto.whnf=function(e){
    stats.whnf.q++;
    if(!Array.isArray(e)) return base.whnf.call(this,e);
    const key=this.localDefs?ctxKey(this,this._activeCtx??[]):"";
    let slot=this.__eccWhnf.get(e);
    if(this.localDefs){
      if(!(slot instanceof Map)){slot=new Map();this.__eccWhnf.set(e,slot);}
      if(slot.has(key)){stats.whnf.h++;return slot.get(key);}
      const out=base.whnf.call(this,e); slot.set(key,out); return out;
    }
    if(slot!==undefined){stats.whnf.h++;return slot;}
    const out=base.whnf.call(this,e); this.__eccWhnf.set(e,out); return out;
  };
}

function evaluate(mode){
  mode==="compiled"?install():reset();
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0}; let wrong=0,totalSteps=0,totalConstructed=0;
  const before=JSON.parse(JSON.stringify(stats)),t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]++; totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null});
  }
  const delta={};
  for(const [k,v] of Object.entries(stats)) delta[k]={q:v.q-before[k].q,h:v.h-before[k].h};
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:delta,results};
}

const baseline=evaluate("baseline"),candidate=evaluate("compiled"); reset();
if(baseline.wrong||candidate.wrong) throw new Error("wrong verdict");
let protectedChanged=0; const resolved=[],regressions=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});}
  if(b.status==="UNKNOWN"&&c.status!=="UNKNOWN"){
    if(c.status!==c.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(c));
    resolved.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
  }
}
const summary={arena_sha256:sha,budget:1_000_000,
 baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
   stats:candidate.stats,protectedChanged,resolved,regressions},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved.length>0,
 claim_boundary:"Exact completed consequence compiler only: proofType keyed by exact term+context+params; getApp by exact term; same by exact ordered term identities with symmetric reuse; WHNF by exact term and exact LocalDef context. Failures/frontiers are never cached."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/exact-consequence-compiler.json",import.meta.url),JSON.stringify(summary,null,2)+"\n");
console.log("EXACT_CONSEQUENCE_COMPILER "+JSON.stringify(summary));
