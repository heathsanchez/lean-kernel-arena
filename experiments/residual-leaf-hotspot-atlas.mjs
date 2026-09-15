// Zero-semantics innermost-operation hotspot atlas.
//
// Every retained method wrapper pushes its operation name. Each tick is charged
// to the innermost wrapped method currently executing. This complements the
// outer-operation atlas: it reveals which primitive operation actually consumes
// work inside top-level inference/equality.
//
// Diagnostic only: no semantic state, budget, cache, term or verdict changes.
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

const proto=K.Kernel.prototype,retainedTick=proto.tick;
const names=[
  "validate","sortOf","infer","equal","normal","proofType","whnf",
  "substitute","shift","instantiateDeclaration","getApp","same","make",
  "inferProjection","addSingleInductive","instantiateForalls","splitAllForalls",
  "deriveTypeRecursor","structureEtaMatches","functionEtaContract","isUnitLikeType"
];
const retained=new Map(names.map(n=>[n,proto[n]]));
let currentCase=null;
const byCase=new Map();

function bucket(){
  let b=byCase.get(currentCase);
  if(!b){b={};byCase.set(currentCase,b);}
  return b;
}

proto.tick=function(...args){
  const stack=this.__leafAtlasStack;
  const tag=stack?.length?stack[stack.length-1]:"run-other";
  const b=bucket();b[tag]=(b[tag]??0)+1;
  return retainedTick.apply(this,args);
};

for(const name of names){
  const fn=retained.get(name);
  if(typeof fn!=="function")continue;
  proto[name]=function(...args){
    this.__leafAtlasStack??=[];
    this.__leafAtlasStack.push(name);
    try{return fn.apply(this,args);}
    finally{this.__leafAtlasStack.pop();}
  };
}

const results=[];
for(const row of rows){
  currentCase=row.name;byCase.set(currentCase,{});
  const r=K.checkExport(row.input,caps,1_000_000);
  const ticks=byCase.get(currentCase);
  const ranked=Object.entries(ticks).sort((a,b)=>b[1]-a[1]);
  const total=ranked.reduce((n,x)=>n+x[1],0);
  results.push({
    name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
    raw_ticks:total,
    operations:ranked.map(([operation,count])=>({operation,count,fraction:total?count/total:0}))
  });
}
currentCase=null;
for(const [name,fn] of retained)if(typeof fn==="function")proto[name]=fn;
proto.tick=retainedTick;

const report={
  arena_sha256:sha,budget:1000000,results,
  claim_boundary:"Diagnostic only. Each retained tick is attributed to the innermost instrumented retained kernel method on the dynamic call stack. No semantic rule, budget, cache, term, context, verdict or execution order changes."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/residual-leaf-hotspot-atlas.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("RESIDUAL_LEAF_HOTSPOT_ATLAS "+JSON.stringify(report));
