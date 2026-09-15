// Origin attribution for recursive shift/substitute work.
// Charge every tick in a recursive transform to the nearest non-self ancestor that initiated it.
// Instrumentation only; no semantics, budgets, or verdicts change.
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

const residual=[];
for(const row of rows) {
  const r=K.checkExport(row.input,caps,1_000_000);
  if(r.status==="UNKNOWN" && ["budget-exhausted","host-stack-limit"].includes(r.reason)) residual.push(row);
}
if(residual.length!==19) throw new Error("frontier changed: "+residual.length);

const proto=K.Kernel.prototype;
const methods=[
  "run","validate","shift","substitute","lowerBound","functionEtaContract","whnf","same",
  "normal","proofType","equal","instantiateDeclaration","sortOf","infer","inferProjection",
  "instantiateForalls","splitAllForalls","deriveTypeRecursor","addSingleInductive"
];
for(const name of methods) {
  if(typeof proto[name]!=="function") continue;
  const orig=proto[name];
  proto[name]=function(...args){
    this.__originProfile ??={stack:[],ticks:Object.create(null),calls:Object.create(null)};
    const p=this.__originProfile;
    p.stack.push(name);
    try{return orig.apply(this,args);}
    finally{p.stack.pop();}
  };
}

function originFor(stack,target) {
  // Find the outermost contiguous target recursion frame and report its immediate caller.
  let first=stack.length-1;
  while(first>0 && stack[first-1]===target) first--;
  const caller=first>0?stack[first-1]:"<root>";
  return caller+"->"+target;
}

const origTick=proto.tick;
proto.tick=function(...args){
  this.__originProfile ??={stack:[],ticks:Object.create(null),calls:Object.create(null)};
  const st=this.__originProfile.stack;
  const top=st.at(-1);
  if(top==="shift"||top==="substitute") {
    const key=originFor(st,top);
    this.__originProfile.ticks[key]=(this.__originProfile.ticks[key]??0)+1;
  }
  return origTick.apply(this,args);
};

// Count top-level transform entries by origin, not recursive self calls.
for(const target of ["shift","substitute"]) {
  const wrapped=proto[target];
  proto[target]=function(...args){
    this.__originProfile ??={stack:[],ticks:Object.create(null),calls:Object.create(null)};
    const st=this.__originProfile.stack;
    const parent=st.at(-1)??"<root>";
    const recursive=parent===target;
    if(!recursive) {
      const key=parent+"->"+target;
      this.__originProfile.calls[key]=(this.__originProfile.calls[key]??0)+1;
    }
    return wrapped.apply(this,args);
  };
}

const origResult=proto.result;
proto.result=function(...args){
  const r=origResult.apply(this,args);
  r.__originProfile=this.__originProfile??{stack:[],ticks:{},calls:{}};
  return r;
};

const budget=1_000_000,results=[];
for(const row of residual) {
  const r=K.checkExport(row.input,caps,budget);
  const p=r.__originProfile??{ticks:{},calls:{}};
  const ranked=Object.entries(p.ticks).sort((a,b)=>b[1]-a[1]).map(([origin,ticks])=>({
    origin,ticks,share:ticks/Math.max(1,r.steps??budget),calls:p.calls[origin]??0
  }));
  const item={name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,origins:ranked.slice(0,12)};
  results.push(item);
  console.log("BINDER_ORIGIN_RESIDUAL "+JSON.stringify(item));
}

const aggregate={};
for(const x of results) for(const h of x.origins) {
  const a=aggregate[h.origin]??={origin:h.origin,ticks:0,calls:0,cases:0};
  a.ticks+=h.ticks;a.calls+=h.calls;a.cases++;
}
const ranked=Object.values(aggregate).sort((a,b)=>b.ticks-a.ticks);
const summary={
  arena_sha256:sha,budget,residual_count:results.length,aggregate:ranked,
  scope:"Instrumentation only. Recursive shift/substitute ticks are charged to the non-self call site that initiated the transform."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/binder-origins.json",import.meta.url),JSON.stringify({summary,results},null,2));
console.log("BINDER_ORIGIN_SUMMARY "+JSON.stringify(summary));
