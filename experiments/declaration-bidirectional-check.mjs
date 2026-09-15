// Prospective declaration-boundary bidirectional checking.
//
// The retained declaration gate checks a value by fully inferring its type and
// then comparing that materialized result with the already-known declared type.
// For lambda/application-heavy declarations this can construct and normalize a
// large intermediate type that the declaration itself already supplies.
//
// This separator uses the declared type only as an expected-type guide:
//   lambda vs Pi: verify annotation/domain equality, recurse on body/codomain;
//   application: infer only the function type, check the argument against its
//                domain, compare the instantiated codomain to the expectation;
//   residual: fall back to retained infer + retained equality.
//
// Every candidate attempt is transactional. On UNKNOWN/REJECT/stack obstruction
// or unsupported expected shape, steps/frontier/budget are restored and the
// retained infer path runs unchanged. A successful route returns the exact
// declared expected type to the retained outer equality check.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");

const wanted=[
  "good/perf/fueled-chain.ndjson",
  "good/perf/magma-list-deep-n21.ndjson",
  "good/perf/magma-list-pair-n7.ndjson",
  "good/perf/shared-subterm.ndjson"
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
if(focusRows.length!==4)throw new Error("focus rows missing");

const proto=K.Kernel.prototype;
const retainedRun=proto.run,retainedInfer=proto.infer;
const stats={
  rootQueries:0,eligible:0,successes:0,fallbacks:0,
  lambdaChecks:0,appChecks:0,terminalChecks:0,unsupported:0
};
class BidirMiss extends Error {}

function checkExpected(k,e,expected,ctx,mode){
  if(!Array.isArray(e)||!Array.isArray(expected))throw new BidirMiss("nonterm");

  if(e[0]==="lam"){
    const w=k.whnf(expected);
    if(!Array.isArray(w)||w[0]!=="pi"){stats.unsupported++;throw new BidirMiss("lambda-not-pi");}
    stats.lambdaChecks++;
    k.tick();k.need("binders");
    k.sortOf(e[1],ctx);
    k.equal(e[1],w[1],ctx);
    checkExpected(k,e[2],w[2],[...ctx,e[1]],mode);
    return;
  }

  if(mode==="lambda-app" && e[0]==="app"){
    stats.appChecks++;
    k.tick();k.need("application");
    const fty=k.whnf(retainedInfer.call(k,e[1],ctx));
    if(!Array.isArray(fty)||fty[0]!=="pi"){stats.unsupported++;throw new BidirMiss("app-not-pi");}
    checkExpected(k,e[2],fty[1],ctx,mode);
    const out=k.substitute(fty[2],e[2]);
    k.equal(out,expected,ctx);
    return;
  }

  stats.terminalChecks++;
  const actual=retainedInfer.call(k,e,ctx);
  k.equal(actual,expected,ctx);
}

function install(mode){
  proto.run=retainedRun;proto.infer=retainedInfer;
  if(mode==="baseline")return;

  proto.run=function(term,expected,declarations=[],parameters=[]){
    this.__declBidirExpected=new WeakMap();
    for(const d of declarations){
      if(d && Array.isArray(d.value) && Array.isArray(d.type))
        this.__declBidirExpected.set(d.value,{name:d.name,expected:d.type});
    }
    return retainedRun.call(this,term,expected,declarations,parameters);
  };

  proto.infer=function(e,ctx=[]){
    if(this.__declBidirDepth || !Array.isArray(e) || ctx.length!==0)
      return retainedInfer.call(this,e,ctx);
    const target=this.__declBidirExpected?.get(e);
    if(!target || target.name!==this.currentDeclaration)
      return retainedInfer.call(this,e,ctx);

    stats.rootQueries++;
    if(e[0]!=="lam" && !(mode==="lambda-app"&&e[0]==="app"))
      return retainedInfer.call(this,e,ctx);
    stats.eligible++;

    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    this.__declBidirDepth=1;
    try{
      checkExpected(this,e,target.expected,ctx,mode);
      this.__declBidirDepth=0;
      this.budget=snap.budget;
      stats.successes++;
      return target.expected;
    }catch(err){
      this.__declBidirDepth=0;
      this.budget=snap.budget;
      if(!(err instanceof Stop || err instanceof RangeError || err instanceof BidirMiss))throw err;
      this.steps=snap.steps;this.conversionFrontier=snap.frontier;
      stats.fallbacks++;
      return retainedInfer.call(this,e,ctx);
    }
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
  baseline:evaluate("baseline",focusRows,1_000_000),
  lambda:evaluate("lambda",focusRows,1_000_000),
  lambdaApp:evaluate("lambda-app",focusRows,1_000_000)
};
for(const x of Object.values(focus))if(x.wrong)throw new Error("focus wrong verdict");

function score(x){
  const accepts=x.results.filter(r=>r.status==="ACCEPT").length;
  const total=x.results.reduce((n,r)=>n+(r.status==="ACCEPT"?(r.steps??0):1_000_001),0);
  return [-accepts,total,x.totalConstructed,x.elapsed_ms];
}
const candidates=[focus.lambda,focus.lambdaApp].sort((a,b)=>{
  const x=score(a),y=score(b);
  for(let i=0;i<x.length;i++)if(x[i]!==y[i])return x[i]-y[i];
  return a.mode.localeCompare(b.mode);
});
const winnerMode=candidates[0].mode;
let winner=candidates[0];

let cliff=null;
if(!winner.results.some(r=>r.status==="ACCEPT")){
  cliff=evaluate(winnerMode,focusRows,2_000_000);
  if(cliff.wrong)throw new Error("cliff wrong verdict");
  if(cliff.results.some(r=>r.status==="ACCEPT"))winner=cliff;
}

let full=null;
if(winner.results.some(r=>r.status==="ACCEPT")){
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
  const cand=evaluate(winnerMode,allRows,1_000_000),base=evaluate("baseline",allRows,1_000_000);
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
    candidate:{mode:winnerMode,counts:cand.counts,totalSteps:cand.totalSteps,totalConstructed:cand.totalConstructed,
      elapsed_ms:cand.elapsed_ms,stats:cand.stats,protectedChanged,resolved,regressions,remaining},
    lawful:cand.wrong===0&&protectedChanged===0,
    promotable:cand.wrong===0&&protectedChanged===0&&resolved.length>0
  };
}
install("baseline");

const report={
  arena_sha256:sha,focus,winner_mode:winnerMode,cliff,full,
  claim_boundary:"Execution-only bidirectional declaration checking. The declared type is used as an expected-type guide for lambda/application structure, but every domain/result obligation is discharged by retained sort/infer/equality rules. Attempts are transactional; any unresolved/rejected/stack-obstructed route restores steps/frontier and replays retained inference. No typing or equality rule is added."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/declaration-bidirectional-check.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("DECLARATION_BIDIRECTIONAL_CHECK "+JSON.stringify(report));
