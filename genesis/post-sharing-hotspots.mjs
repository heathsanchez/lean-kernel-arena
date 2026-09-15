// Residual hotspot atlas after the smallest lawful sharing repair: hash-consing only.
// Diagnostic only; same semantics and 1M budget.
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
const originalMake=proto.make;

function objectId(kernel,x){
  kernel.__ids??=new WeakMap(); kernel.__nextId??=1;
  if(!kernel.__ids.has(x)) kernel.__ids.set(x,kernel.__nextId++);
  return kernel.__ids.get(x);
}
function scalarKey(x){
  if(typeof x==="string") return "s:"+x;
  if(typeof x==="number") return "n:"+x;
  if(typeof x==="boolean") return "b:"+(x?1:0);
  if(x===null) return "null";
  return typeof x+":"+String(x);
}
proto.make=function(...xs){
  this.tick();
  this.__cons??=new Map();
  const key=xs.map(x=>Array.isArray(x)?"a:"+objectId(this,x):scalarKey(x)).join("|");
  const old=this.__cons.get(key);
  if(old!==undefined) return old;
  this.allocations++;
  this.__cons.set(key,xs);
  objectId(this,xs);
  return xs;
};

// First identify the post-sharing residual.
const post=[];
for(const row of rows){
  const r=K.checkExport(row.input,caps,1_000_000);
  if(r.status==="UNKNOWN"&&["budget-exhausted","host-stack-limit"].includes(r.reason)) post.push(row);
}
if(post.length!==18) throw new Error("post-sharing residual changed: "+post.length);

// Attribute ticks across semantic operations under hash-consing.
const methods=[
  "validate","shift","substitute","lowerBound","functionEtaContract","whnf","same",
  "normal","proofType","equal","instantiateDeclaration","sortOf","infer","inferProjection",
  "instantiateForalls","splitAllForalls","deriveTypeRecursor","addSingleInductive",
  "getApp","hasConst","isUnitLikeType","structureEtaMatches"
];
for(const name of methods){
  if(typeof proto[name]!=="function") continue;
  const orig=proto[name];
  proto[name]=function(...args){
    this.__prof??={stack:[],ticks:Object.create(null),calls:Object.create(null)};
    const p=this.__prof;
    p.calls[name]=(p.calls[name]??0)+1;
    p.stack.push(name);
    try{return orig.apply(this,args);}
    finally{p.stack.pop();}
  };
}
const origTick=proto.tick;
proto.tick=function(...args){
  this.__prof??={stack:[],ticks:Object.create(null),calls:Object.create(null)};
  const top=this.__prof.stack.at(-1)??"<unattributed>";
  this.__prof.ticks[top]=(this.__prof.ticks[top]??0)+1;
  return origTick.apply(this,args);
};
const origResult=proto.result;
proto.result=function(...args){
  const r=origResult.apply(this,args);
  r.__prof=this.__prof??{ticks:{},calls:{}};
  return r;
};

const results=[];
for(const row of post){
  const r=K.checkExport(row.input,caps,1_000_000);
  const p=r.__prof??{ticks:{},calls:{}};
  const top=Object.entries(p.ticks).sort((a,b)=>b[1]-a[1]).slice(0,12).map(([op,ticks])=>({
    op,ticks,share:ticks/Math.max(1,r.steps??1_000_000),calls:p.calls[op]??0
  }));
  const item={name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,top};
  results.push(item);
  console.log("POST_SHARING_RESIDUAL "+JSON.stringify(item));
}
const agg={};
for(const x of results) for(const h of x.top){
  const a=agg[h.op]??={op:h.op,ticks:0,calls:0,cases:0};
  a.ticks+=h.ticks;a.calls+=h.calls;a.cases++;
}
const summary={
  arena_sha256:sha,budget:1_000_000,residual_count:results.length,
  aggregate:Object.values(agg).sort((a,b)=>b.ticks-a.ticks),
  scope:"Diagnostic under hash-consing only; no semantic rule changes."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/post-sharing-hotspots.json",import.meta.url),JSON.stringify({summary,results},null,2));
console.log("POST_SHARING_SUMMARY "+JSON.stringify(summary));

proto.make=originalMake;
