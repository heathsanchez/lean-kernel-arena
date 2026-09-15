// Exact structural-key WHNF consequence cache for the ordinary kernel only.
//
// The residual leaf atlas shows WHNF is the largest primitive cost in the deep
// and pair magma families. Base-kernel WHNF depends on immutable syntax plus the
// monotonically growing declaration environment. A successful WHNF result can
// therefore be reused for the exact same syntax later in the same run: existing
// declarations never change, and a term referring to an undeclared constant
// could not have produced a successful result earlier.
//
// LocalDef execution is deliberately excluded because WHNF(var) there depends on
// the active local-definition context; a prior LocalDef WHNF cache was falsified
// by folded-constant-last.
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
const focusRows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(focusRows.length!==5)throw new Error("focus rows missing");

const proto=K.Kernel.prototype;
const retainedRun=proto.run,retainedWhnf=proto.whnf;
const END=Symbol("end");
const stats={queries:0,hits:0,stores:0,canonNodes:0,localBypass:0};

function ensure(k){
  k.__whnfCanonWeak??=new WeakMap();
  k.__whnfCanonRoot??=new Map();
  k.__structWhnfCache??=new WeakMap();
}
function rep(k,e){
  if(!Array.isArray(e))return e;
  ensure(k);
  const old=k.__whnfCanonWeak.get(e);
  if(old!==undefined)return old;
  const xs=new Array(e.length);let changed=false;
  for(let i=0;i<e.length;i++){
    const y=Array.isArray(e[i])?rep(k,e[i]):e[i];
    xs[i]=y;if(y!==e[i])changed=true;
  }
  let node=k.__whnfCanonRoot;
  for(const x of xs){
    let next=node.get(x);
    if(!(next instanceof Map)){next=new Map();node.set(x,next);}
    node=next;
  }
  let r=node.get(END);
  if(r===undefined){r=changed?xs:e;node.set(END,r);stats.canonNodes++;}
  k.__whnfCanonWeak.set(e,r);k.__whnfCanonWeak.set(r,r);
  return r;
}

function install(enabled){
  proto.run=retainedRun;proto.whnf=retainedWhnf;
  if(!enabled)return;
  proto.run=function(...args){
    this.__whnfCanonWeak=new WeakMap();
    this.__whnfCanonRoot=new Map();
    this.__structWhnfCache=new WeakMap();
    return retainedRun.apply(this,args);
  };
  proto.whnf=function(e){
    if(this.localDefs===true || !Array.isArray(e)){
      if(this.localDefs===true)stats.localBypass++;
      return retainedWhnf.call(this,e);
    }
    stats.queries++;
    const r=rep(this,e);
    if(this.__structWhnfCache?.has(r)){stats.hits++;return this.__structWhnfCache.get(r);}
    const out=retainedWhnf.call(this,e);
    this.__structWhnfCache.set(r,out);stats.stores++;
    return out;
  };
}

function evaluate(mode,enabled,subset,budget){
  install(enabled);
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

const baseline=evaluate("baseline",false,focusRows,1_000_000);
const candidate=evaluate("candidate",true,focusRows,1_000_000);
if(baseline.wrong||candidate.wrong)throw new Error("focus wrong verdict");

let cliff=null;
if(!candidate.results.some(r=>r.status==="ACCEPT")){
  cliff=evaluate("candidate-cliff",true,focusRows,2_000_000);
  if(cliff.wrong)throw new Error("cliff wrong verdict");
}

let full=null;
if(candidate.results.some(r=>r.status==="ACCEPT") || cliff?.results.some(r=>r.status==="ACCEPT")){
  const pyAll=[
    "import io,tarfile,json,sys",
    "data=sys.stdin.buffer.read();rows=[]",
    "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
    "  for m in a:",
    "    p=m.name.split('/')",
    "    if not m.isfile() or not m.name.endswith('.ndjson') or m.size>2000000: continue",
    "    e='ACCEPT' if 'good' in p else 'REJECT' if 'bad' in p else None",
    "    if e: rows.append({'name':m.name,'expected':e,'input':a.extractfile(m).read().decode('utf-8')})",
    "print(json.dumps(rows))"
  ].join("\n");
  const allRows=JSON.parse(execFileSync("python3",["-c",pyAll],{input:data,maxBuffer:50000000,timeout:10000}));
  const cand=evaluate("candidate-full",true,allRows,1_000_000);
  const base=evaluate("baseline-full",false,allRows,1_000_000);
  if(cand.wrong||base.wrong)throw new Error("full wrong verdict");
  let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
  for(let i=0;i<allRows.length;i++){
    const b=base.results[i],c=cand.results[i];
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
    baseline:{counts:base.counts,totalSteps:base.totalSteps,totalConstructed:base.totalConstructed,elapsed_ms:base.elapsed_ms},
    candidate:{counts:cand.counts,totalSteps:cand.totalSteps,totalConstructed:cand.totalConstructed,elapsed_ms:cand.elapsed_ms,
      stats:cand.stats,protectedChanged,resolved,regressions,remaining},
    lawful:cand.wrong===0&&protectedChanged===0,
    promotable:cand.wrong===0&&protectedChanged===0&&resolved.length>0
  };
}
install(false);

const report={
  arena_sha256:sha,budget:1000000,baseline,candidate,cliff,full,
  claim_boundary:"Execution consequence reuse only in the ordinary kernel. Cache key is an exact structural representative of immutable syntax. Values are stored only after retained WHNF returns successfully. LocalDef execution is excluded because its WHNF depends on active local definitions."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/structural-whnf-keys.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("STRUCTURAL_WHNF_KEYS "+JSON.stringify(report));
