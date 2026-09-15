// Prospective bidirectional lambda checking for LocalDef application inference.
//
// The retained checker is inferential: for f a it infers the complete type of
// a and then compares that inferred type to f's Pi domain. When a is a lambda
// and the expected domain is itself a Pi, that constructs a potentially huge
// duplicated dependent type only to compare it immediately.
//
// This experiment checks lambdas directly against the expected Pi telescope:
// annotation type is checked/equal to the expected domain, then the body is
// checked against the expected codomain under the binder. All non-lambda cases
// preserve the retained infer-then-compare path.
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
if(rows.length!==188)throw new Error("Arena row count changed");

const proto=K.Kernel.prototype;
const retainedInfer=proto.infer;
const stats={appChecks:0,lambdaExpected:0,lambdaDirect:0,fallback:0,maxLambdaDepth:0};

function checkExpected(k,e,expected,ctx,depth=0){
  if(Array.isArray(e)&&e[0]==="lam"){
    let w;
    try{w=k.whnf(expected);}catch(_){w=expected;}
    if(Array.isArray(w)&&w[0]==="pi"){
      stats.lambdaExpected++;
      stats.maxLambdaDepth=Math.max(stats.maxLambdaDepth,depth+1);
      // Mirror retained lambda inference obligations, but do not construct the
      // whole inferred Pi type only to compare it afterward.
      k.tick();k.need("binders");
      k.sortOf(e[1],ctx);
      k.equal(e[1],w[1],ctx);
      stats.lambdaDirect++;
      return checkExpected(k,e[2],w[2],[...ctx,e[1]],depth+1);
    }
  }
  stats.fallback++;
  k.equal(k.infer(e,ctx),expected,ctx);
}

function install(enabled){
  proto.infer=retainedInfer;
  if(!enabled)return;
  proto.infer=function(e,ctx=[]){
    if(this.localDefs!==true || !Array.isArray(e) || e[0]!=="app")
      return retainedInfer.call(this,e,ctx);

    stats.appChecks++;
    this.tick();this.need("application");
    const f=this.whnf(this.infer(e[1],ctx));
    if(!Array.isArray(f)||f[0]!=="pi") this.reject("not-a-function");
    checkExpected(this,e[2],f[1],ctx,0);
    return this.substitute(f[2],e[2]);
  };
}

function evalRows(mode,enabled,subset){
  install(enabled);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null,
      fallback_mode:r.fallback_mode??null,fallback_attempt_reason:r.fallback_attempt_reason??null});
  }
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results};
}

const focusRows=rows.filter(r=>r.name.endsWith("good/perf/fueled-chain.ndjson"));
const focus=evalRows("focus",true,focusRows);
console.log("BIDIR_LOCALDEF_LAMBDA_FOCUS "+JSON.stringify(focus));
if(focus.wrong)throw new Error("focus wrong");
if(focus.results[0]?.status!=="ACCEPT"){
  install(false);
  console.log("BIDIR_LOCALDEF_LAMBDA_STOP "+JSON.stringify({reason:"fueled-not-closed",focus}));
  process.exit(0);
}

const candidate=evalRows("candidate",true,rows);
const baseline=evalRows("baseline",false,rows);
install(false);
if(candidate.wrong||baseline.wrong)throw new Error("wrong verdict");
let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"){
    if(c.status!=="UNKNOWN"&&c.status===c.expected)
      resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
    else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,frontier_declaration:c.frontier_declaration});
  }
}
const report={arena_sha256:sha,budget:1000000,focus,
  baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
    elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved.some(r=>r.name.endsWith("fueled-chain.ndjson")),
  claim_boundary:"Typing execution order only in LocalDef application inference. When an argument is a lambda and the expected function domain WHNFs to Pi, the lambda annotation is checked against the expected Pi domain and its body is checked recursively against the expected codomain under the binder. All non-lambda cases retain infer-then-compare. No typing judgment or conversion rule is added."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/bidir-localdef-lambda.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("BIDIR_LOCALDEF_LAMBDA "+JSON.stringify(report));
