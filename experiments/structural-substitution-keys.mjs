// Exact structural-key substitution consequence cache.
//
// Retained substitution memoization keys by root object identity + argument
// object identity + depth. The residual atlas shows substitution/materialization
// dominating shared-subterm and the magma families. Structurally identical
// immutable terms arriving through distinct parser/construction identities can
// therefore repay the same exact substitution.
//
// This separator interns syntax ONLY for cache keys. It does not replace terms,
// alter de-Bruijn indices, normalize, infer, reduce, or add any equality rule.
// A hit returns a previously completed retained substitution for exactly the
// same syntax root, syntax argument and numeric depth.
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
const retainedRun=proto.run,retainedSubstitute=proto.substitute;
const END=Symbol("end");
const stats={queries:0,hits:0,stores:0,canonNodes:0};

function ensure(k){
  k.__substCanonWeak??=new WeakMap();
  k.__substCanonRoot??=new Map();
  k.__structSubstCache??=new WeakMap();
}
function rep(k,e){
  if(!Array.isArray(e))return e;
  ensure(k);
  const old=k.__substCanonWeak.get(e);
  if(old!==undefined)return old;
  const xs=new Array(e.length);let changed=false;
  for(let i=0;i<e.length;i++){
    const y=Array.isArray(e[i])?rep(k,e[i]):e[i];
    xs[i]=y;if(y!==e[i])changed=true;
  }
  let node=k.__substCanonRoot;
  for(const x of xs){
    let next=node.get(x);
    if(!(next instanceof Map)){next=new Map();node.set(x,next);}
    node=next;
  }
  let r=node.get(END);
  if(r===undefined){r=changed?xs:e;node.set(END,r);stats.canonNodes++;}
  k.__substCanonWeak.set(e,r);k.__substCanonWeak.set(r,r);
  return r;
}
function cacheMap(k,r,a){
  ensure(k);
  let byR=k.__structSubstCache.get(r);
  if(!byR){byR=new WeakMap();k.__structSubstCache.set(r,byR);}
  let byD=byR.get(a);
  if(!byD){byD=new Map();byR.set(a,byD);}
  return byD;
}

function install(mode){
  proto.run=retainedRun;proto.substitute=retainedSubstitute;
  if(mode==="baseline")return;
  proto.run=function(...args){
    this.__substCanonWeak=new WeakMap();
    this.__substCanonRoot=new Map();
    this.__structSubstCache=new WeakMap();
    return retainedRun.apply(this,args);
  };
  proto.substitute=function(root,arg,depth=0){
    if(!Array.isArray(root)||!Array.isArray(arg))
      return retainedSubstitute.call(this,root,arg,depth);
    stats.queries++;
    const rr=mode==="both"?rep(this,root):root;
    const aa=rep(this,arg);
    const m=cacheMap(this,rr,aa);
    if(m.has(depth)){stats.hits++;return m.get(depth);}
    const out=retainedSubstitute.call(this,root,arg,depth);
    m.set(depth,out);stats.stores++;
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
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null,
      fallback_mode:r.fallback_mode??null,fallback_attempt_reason:r.fallback_attempt_reason??null});
  }
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  return {mode,budget,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results};
}

const focus={
  baseline:evaluate("baseline",rows,1_000_000),
  arg:evaluate("arg",rows,1_000_000),
  both:evaluate("both",rows,1_000_000)
};
for(const x of Object.values(focus))if(x.wrong)throw new Error("focus wrong verdict");

function score(x){
  const accepts=x.results.filter(r=>r.status==="ACCEPT").length;
  const resolvedBudget=x.results.reduce((n,r)=>n+(r.status==="ACCEPT"?(r.steps??0):1_000_001),0);
  return [-accepts,resolvedBudget,x.totalSteps,x.totalConstructed,x.elapsed_ms];
}
const candidates=[focus.arg,focus.both].sort((a,b)=>{
  const x=score(a),y=score(b);
  for(let i=0;i<x.length;i++)if(x[i]!==y[i])return x[i]-y[i];
  return a.mode.localeCompare(b.mode);
});
const winnerMode=candidates[0].mode;
let winner=candidates[0];

let cliff=null;
if(!winner.results.some(r=>r.status==="ACCEPT")){
  const cliffNames=new Set([
    "good/perf/shared-subterm.ndjson",
    "good/perf/magma-list-deep-n21.ndjson",
    "good/perf/magma-list-pair-n7.ndjson"
  ]);
  cliff=evaluate(winnerMode,rows.filter(r=>cliffNames.has(r.name)),2_000_000);
  if(cliff.wrong)throw new Error("cliff wrong verdict");
  if(cliff.results.some(r=>r.status==="ACCEPT"))winner=cliff;
}

let full=null;
if(winner.results.some(r=>r.status==="ACCEPT")){
  const candidate=evaluate(winnerMode,
    rows.length===188?rows:JSON.parse(execFileSync("python3",["-c",[
      "import io,tarfile,json,sys",
      "data=sys.stdin.buffer.read();rows=[]",
      "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
      "  for m in a:",
      "    p=m.name.split('/')",
      "    if not m.isfile() or not m.name.endswith('.ndjson') or m.size>2000000: continue",
      "    e='ACCEPT' if 'good' in p else 'REJECT' if 'bad' in p else None",
      "    if e: rows.append({'name':m.name,'expected':e,'input':a.extractfile(m).read().decode('utf-8')})",
      "print(json.dumps(rows))"
    ].join("\n")],{input:data,maxBuffer:50000000,timeout:10000})),
    1_000_000);
  const allRows=candidate.results.length===188
    ? JSON.parse(execFileSync("python3",["-c",[
        "import io,tarfile,json,sys",
        "data=sys.stdin.buffer.read();rows=[]",
        "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
        "  for m in a:",
        "    p=m.name.split('/')",
        "    if not m.isfile() or not m.name.endswith('.ndjson') or m.size>2000000: continue",
        "    e='ACCEPT' if 'good' in p else 'REJECT' if 'bad' in p else None",
        "    if e: rows.append({'name':m.name,'expected':e,'input':a.extractfile(m).read().decode('utf-8')})",
        "print(json.dumps(rows))"
      ].join("\n")],{input:data,maxBuffer:50000000,timeout:10000}))
    : rows;
  const baseline=evaluate("baseline",allRows,1_000_000);
  if(candidate.wrong||baseline.wrong)throw new Error("full wrong verdict");
  let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
  for(let i=0;i<allRows.length;i++){
    const b=baseline.results[i],c=candidate.results[i];
    if(b.status!=="UNKNOWN"&&c.status!==b.status){
      protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
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
  claim_boundary:"Execution consequence reuse only. Cache keys are exact structural representatives of immutable term syntax (argument-only or both root and argument) plus exact numeric substitution depth. Values are stored only after the retained substitute completes successfully. No normalization, alpha-equivalence, definitional equality, typing or reduction rule is introduced."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/structural-substitution-keys.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("STRUCTURAL_SUBSTITUTION_KEYS "+JSON.stringify(report));
