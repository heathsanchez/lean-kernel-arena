// Behavioral-neutral hotspot attribution for the frozen resource frontier.
// Wraps Kernel methods and charges each tick to the innermost active core operation.
// No semantic rule, budget, input, or verdict policy is changed.
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

// Re-identify the exact residual from the frozen 1M-step present.
const residual=[];
for(const row of rows) {
  const r=K.checkExport(row.input,caps,1_000_000);
  if(r.status==="UNKNOWN" && ["budget-exhausted","host-stack-limit"].includes(r.reason))
    residual.push(row);
}
if(residual.length!==19) throw new Error("frontier changed: "+residual.length);

const methods=[
  "validate","shift","substitute","lowerBound","functionEtaContract","whnf","same",
  "structureEtaMatches","normal","proofType","equal","instantiateDeclaration",
  "sortOf","infer","inferProjection","instantiateForalls","splitAllForalls",
  "isExactIndApp","deriveTypeRecursor","addSingleInductive"
];

const proto=K.Kernel.prototype;
const originals=new Map();
for(const name of methods) {
  if(typeof proto[name]!=="function") continue;
  const orig=proto[name]; originals.set(name,orig);
  proto[name]=function(...args){
    this.__profile ??={stack:[],calls:Object.create(null),ticks:Object.create(null),maxDepth:Object.create(null)};
    const p=this.__profile;
    p.calls[name]=(p.calls[name]??0)+1;
    p.stack.push(name);
    p.maxDepth[name]=Math.max(p.maxDepth[name]??0,p.stack.length);
    try { return orig.apply(this,args); }
    finally { p.stack.pop(); }
  };
}
const origTick=proto.tick;
proto.tick=function(...args){
  this.__profile ??={stack:[],calls:Object.create(null),ticks:Object.create(null),maxDepth:Object.create(null)};
  const p=this.__profile, top=p.stack.at(-1)??"<unattributed>";
  p.ticks[top]=(p.ticks[top]??0)+1;
  return origTick.apply(this,args);
};

// checkExport constructs Kernel internally, so capture each instance's final profile via result().
const origResult=proto.result;
proto.result=function(...args){
  const r=origResult.apply(this,args);
  r.__profile=this.__profile??{stack:[],calls:{},ticks:{},maxDepth:{}};
  return r;
};

const budget=1_000_000;
const results=[];
for(const row of residual) {
  const r=K.checkExport(row.input,caps,budget);
  // checkExport spreads Kernel.result(), retaining __profile.
  const p=r.__profile??{calls:{},ticks:{},maxDepth:{}};
  const ranked=Object.entries(p.ticks).sort((a,b)=>b[1]-a[1]).map(([op,ticks])=>({
    op,ticks,share:ticks/Math.max(1,r.steps??budget),calls:p.calls[op]??0,max_depth:p.maxDepth[op]??0
  }));
  const item={name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,top:ranked.slice(0,8)};
  results.push(item);
  console.log("HOTSPOT_RESIDUAL "+JSON.stringify(item));
}

const aggregate={};
for(const x of results) for(const h of x.top) {
  const a=aggregate[h.op]??={op:h.op,ticks:0,calls:0,cases:0};
  a.ticks+=h.ticks;a.calls+=h.calls;a.cases++;
}
const rankedAgg=Object.values(aggregate).sort((a,b)=>b.ticks-a.ticks);
const summary={
  arena_sha256:sha,budget,residual_count:results.length,
  aggregate_top:rankedAgg.slice(0,12),
  scope:"Instrumentation only: ticks charged to innermost active Kernel method; no semantic or verdict behavior changed."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/resource-hotspots.json",import.meta.url),JSON.stringify({summary,results},null,2));
console.log("HOTSPOT_SUMMARY "+JSON.stringify(summary));
