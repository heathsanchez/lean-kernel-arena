// Zero-semantics residual hotspot atlas.
//
// Counts actual tick invocations by the outermost checker operation. Nested work
// inherits the outermost tag, so e.g. proofType/infer/normal work initiated by
// equal is charged to equal. This changes no budget, result, term, cache or rule.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");

const wanted=[
  "good/perf/fueled-chain.ndjson",
  "good/perf/magma-list-deep-n21.ndjson",
  "good/perf/magma-list-deep-n36.ndjson",
  "good/perf/shared-subterm.ndjson",
  "good/perf/magma-list-pair-n21.ndjson",
  "good/perf/magma-list-pair-n7.ndjson"
];
const py=[
  "import io,tarfile,json,sys",
  "wanted=set("+JSON.stringify(wanted)+")",
  "data=sys.stdin.buffer.read();rows=[]",
  "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
  "  for m in a:",
  "    p='/'.join(m.name.split('/')[-3:])",
  "    if m.isfile() and p in wanted:",
  "      rows.append({'name':p,'expected':'ACCEPT','input':a.extractfile(m).read().decode('utf-8')})",
  "print(json.dumps(rows))"
].join("\n");
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==6)throw new Error("residual rows missing");

const proto=K.Kernel.prototype;
const retainedTick=proto.tick;
const names=[
  "validate","sortOf","infer","equal","normal","proofType","whnf",
  "substitute","shift","instantiateDeclaration","getApp","same",
  "inferProjection","addSingleInductive"
];
const retained=new Map(names.map(n=>[n,proto[n]]));
let currentCase=null;
const rawByCase=new Map();

function bucket(){
  let b=rawByCase.get(currentCase);
  if(!b){b={};rawByCase.set(currentCase,b);}
  return b;
}

proto.tick=function(...args){
  const tag=this.__atlasOuter??"run-other";
  const b=bucket();b[tag]=(b[tag]??0)+1;
  return retainedTick.apply(this,args);
};

for(const name of names){
  const fn=retained.get(name);
  if(typeof fn!=="function")continue;
  proto[name]=function(...args){
    if(this.__atlasOuter)return fn.apply(this,args);
    this.__atlasOuter=name;
    try{return fn.apply(this,args);}
    finally{this.__atlasOuter=null;}
  };
}

const results=[];
for(const row of rows){
  currentCase=row.name;
  rawByCase.set(currentCase,{});
  const r=K.checkExport(row.input,caps,1_000_000);
  const ticks=rawByCase.get(currentCase);
  const ranked=Object.entries(ticks).sort((a,b)=>b[1]-a[1]);
  const total=ranked.reduce((n,x)=>n+x[1],0);
  results.push({
    name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
    raw_ticks:total,
    operations:ranked.map(([operation,count])=>({
      operation,count,fraction:total?count/total:0
    }))
  });
}
currentCase=null;

for(const [name,fn] of retained)proto[name]=fn;
proto.tick=retainedTick;

const report={
  arena_sha256:sha,budget:1000000,results,
  claim_boundary:"Diagnostic only. Counts calls to the retained semantic tick by the outermost retained checker operation. No semantic rule, budget, cache, term, context, verdict or execution ordering is changed."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/residual-hotspot-atlas.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("RESIDUAL_HOTSPOT_ATLAS "+JSON.stringify(report));
