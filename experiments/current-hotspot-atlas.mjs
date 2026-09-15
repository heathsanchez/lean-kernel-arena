// Current retained-kernel hotspot atlas.
// Instrumentation only: attributes charged semantic ticks to the innermost
// retained operation on the live residual frontier. No verdict/budget behavior
// is changed.
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
if(rows.length!==188) throw new Error("Arena row count changed");

const budget=1_000_000;
const residual=[];
const baselineCounts={ACCEPT:0,REJECT:0,UNKNOWN:0};
for(const row of rows){
  const r=K.checkExport(row.input,caps,budget);
  baselineCounts[r.status]=(baselineCounts[r.status]??0)+1;
  if(r.status!=="UNKNOWN"&&r.status!==row.expected) throw new Error("baseline wrong "+row.name);
  if(r.status==="UNKNOWN") residual.push(row);
}
if(!residual.length) throw new Error("expected live residuals");

const proto=K.Kernel.prototype;
const names=[
  "run","validate","shift","substitute","same","whnf","normal","proofType","equal",
  "instantiateDeclaration","sortOf","infer","getApp","appN","hasConst","lowerBound",
  "functionEtaContract","isUnitLikeType","structureEtaMatches","inferProjection",
  "instantiateForalls","splitAllForalls","deriveTypeRecursor","addSingleInductive",
  "constRef","mkBinders","bvars"
];
const originals=new Map();
for(const name of names){
  if(typeof proto[name]!=="function") continue;
  const orig=proto[name]; originals.set(name,orig);
  proto[name]=function(...args){
    this.__hot ??={stack:[],ticks:Object.create(null),calls:Object.create(null),edges:Object.create(null)};
    const p=this.__hot,parent=p.stack.at(-1)??"<root>";
    p.calls[name]=(p.calls[name]??0)+1;
    const edge=parent+"->"+name;p.edges[edge]=(p.edges[edge]??0)+1;
    p.stack.push(name);
    try{return orig.apply(this,args);}
    finally{p.stack.pop();}
  };
}
const originalTick=proto.tick;
proto.tick=function(...args){
  this.__hot ??={stack:[],ticks:Object.create(null),calls:Object.create(null),edges:Object.create(null)};
  const name=this.__hot.stack.at(-1)??"<root>";
  this.__hot.ticks[name]=(this.__hot.ticks[name]??0)+1;
  return originalTick.apply(this,args);
};
const originalResult=proto.result;
proto.result=function(...args){
  const r=originalResult.apply(this,args);
  r.__hot=this.__hot??{ticks:{},calls:{},edges:{}};
  return r;
};

const results=[];
for(const row of residual){
  const r=K.checkExport(row.input,caps,budget),p=r.__hot??{ticks:{},calls:{},edges:{}};
  const ranked=Object.entries(p.ticks).sort((a,b)=>b[1]-a[1])
    .map(([method,ticks])=>({method,ticks,share:ticks/Math.max(1,r.steps??budget),calls:p.calls[method]??0}));
  const edges=Object.entries(p.edges).sort((a,b)=>b[1]-a[1]).slice(0,20)
    .map(([edge,calls])=>({edge,calls}));
  const item={name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,hot:ranked.slice(0,12),edges};
  results.push(item);
  console.log("CURRENT_HOTSPOT_RESIDUAL "+JSON.stringify(item));
}

proto.tick=originalTick;proto.result=originalResult;
for(const [name,orig] of originals) proto[name]=orig;

const aggregate={};
for(const x of results) for(const h of x.hot){
  const a=aggregate[h.method]??={method:h.method,ticks:0,calls:0,cases:0};
  a.ticks+=h.ticks;a.calls+=h.calls;a.cases++;
}
const ranked=Object.values(aggregate).sort((a,b)=>b.ticks-a.ticks);
const summary={arena_sha256:sha,budget,baseline_counts:baselineCounts,residual_count:residual.length,
  aggregate:ranked,
  scope:"Instrumentation only. Ticks are charged to the innermost retained kernel method on the current live residual frontier."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/current-hotspot-atlas.json",import.meta.url),JSON.stringify({summary,results},null,2));
console.log("CURRENT_HOTSPOT_SUMMARY "+JSON.stringify(summary));
