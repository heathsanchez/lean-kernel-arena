// Prospective separator: batch consecutive beta binders into one exact
// simultaneous de-Bruijn substitution. No typing/conversion law changes.
// The candidate only replaces k sequential beta substitutions when the
// weak-head function exposes k direct lambdas.
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
const originalWhnf=proto.whnf;

function substituteMany(kernel,e,args,depth=0) {
  kernel.tick();
  switch(e[0]) {
    case "sort": case "const": case "nat": case "strlit":
      return e;
    case "var": {
      const i=e[1];
      if(i<depth) return e;
      const j=i-depth;
      if(j<args.length) return kernel.shift(args[args.length-1-j],depth);
      return kernel.make("var",i-args.length);
    }
    case "pi": case "lam":
      return kernel.make(e[0],
        substituteMany(kernel,e[1],args,depth),
        substituteMany(kernel,e[2],args,depth+1));
    case "app":
      return kernel.make("app",
        substituteMany(kernel,e[1],args,depth),
        substituteMany(kernel,e[2],args,depth));
    case "proj":
      return kernel.make("proj",e[1],e[2],substituteMany(kernel,e[3],args,depth));
    case "let":
      return kernel.make("let",
        substituteMany(kernel,e[1],args,depth),
        substituteMany(kernel,e[2],args,depth),
        substituteMany(kernel,e[3],args,depth+1));
    default:
      kernel.unknown("substitution-syntax");
  }
}

function install(enabled) {
  proto.whnf=originalWhnf;
  if(!enabled) return;
  proto.whnf=function(e) {
    if(Array.isArray(e) && e[0]==="app") {
      const args=[]; let head=e;
      while(Array.isArray(head) && head[0]==="app") {
        args.push(head[2]); head=head[1];
      }
      args.reverse();

      let f=originalWhnf.call(this,head);
      let cur=f, consumed=0;
      while(consumed<args.length && Array.isArray(cur) && cur[0]==="lam") {
        consumed++;
        cur=cur[2];
      }

      // One beta does not amortize a traversal. Two or more is the causal
      // separator: replace sequential whole-tree substitution with one pass.
      if(consumed>=2) {
        for(let i=0;i<consumed;i++) { this.tick(); this.need("reduction"); }
        let out=substituteMany(this,cur,args.slice(0,consumed),0);
        for(let i=consumed;i<args.length;i++) out=this.make("app",out,args[i]);
        return this.whnf(out);
      }
    }
    return originalWhnf.call(this,e);
  };
}

const budget=1_000_000;
function evaluate(name,enabled) {
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const start=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;
    totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null,
      fallback_mode:r.fallback_mode??null,stack_attempt_reason:r.stack_attempt_reason??null});
  }
  return {name,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-start,results};
}

const baseline=evaluate("baseline",false);
if(baseline.wrong) throw new Error("baseline wrong");
const residualNames=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
if(residualNames.size!==16) throw new Error("baseline residual changed: "+residualNames.size);

const candidate=evaluate("beta-batch",true);
proto.whnf=originalWhnf;

let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++) {
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status) {
    protectedChanged++;
    regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residualNames.has(r.name)&&r.status!=="UNKNOWN") {
    if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
    resolved++;
    if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
    resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
  } else if(residualNames.has(r.name)) {
    remaining.push({name:r.name,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }
}
const summary={
  arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  claim_boundary:"Prospective execution repair only. Consecutive direct beta binders are eliminated by one exact simultaneous de-Bruijn substitution; no semantic equality, typing rule, or reduction rule is added."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/beta-batch-separator.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("BETA_BATCH_SEPARATOR "+JSON.stringify(summary));
