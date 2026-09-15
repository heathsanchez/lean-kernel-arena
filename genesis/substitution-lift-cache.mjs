// Prospective separator for the origin-forced substitution repair.
// Candidate: within one top-level substitution, cache shift(arg, depth) by binder depth.
// No semantic rule changes; only repeated lifting of the same replacement is compiled.
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
const original=proto.substitute;

function installCachedLift(enabled) {
  proto.substitute=original;
  if(!enabled) return;
  proto.substitute=function(e,arg,depth=0) {
    // Recursive calls from this helper stay inside one explicit traversal and share
    // the lift cache. This is extensionally the same de Bruijn substitution.
    const lifts=new Map();
    const lift=d=>{
      if(!lifts.has(d)) lifts.set(d,this.shift(arg,d));
      return lifts.get(d);
    };
    const go=(x,d)=>{
      this.tick();
      switch(x[0]) {
        case "sort": case "const": case "nat": case "strlit": return x;
        case "var":
          return x[1]===d ? lift(d) : x[1]>d ? this.make("var",x[1]-1) : x;
        case "pi": case "lam":
          return this.make(x[0],go(x[1],d),go(x[2],d+1));
        case "app":
          return this.make("app",go(x[1],d),go(x[2],d));
        case "proj":
          return this.make("proj",x[1],x[2],go(x[3],d));
        case "let":
          return this.make("let",go(x[1],d),go(x[2],d),go(x[3],d+1));
        default:
          this.unknown("substitution-syntax");
      }
    };
    return go(e,depth);
  };
}

const budget=1_000_000;
function evaluate(name,enabled) {
  installCachedLift(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0;
  const start=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,elapsed_ms:r.elapsed_ms??null});
  }
  return {name,counts,wrong,totalSteps,elapsed_ms:Date.now()-start,results};
}

const baseline=evaluate("baseline",false);
if(baseline.wrong) throw new Error("baseline wrong");
const residualNames=new Set(baseline.results.filter(r=>r.status==="UNKNOWN"&&["budget-exhausted","host-stack-limit"].includes(r.reason)).map(r=>r.name));
if(residualNames.size!==19) throw new Error("baseline residual changed: "+residualNames.size);

const candidate=evaluate("lift-cache",true);
proto.substitute=original;

let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[];
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
    resolvedCases.push({name:r.name,status:r.status,steps:r.steps});
  }
}
const summary={
  arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions},
  lawful:candidate.wrong===0&&protectedChanged===0,
  claim_boundary:"Prospective execution repair. Caches only repeated shift(arg,depth) within one substitution traversal; semantics unchanged. Promotion requires integration + ablation + replay."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/substitution-lift-cache.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("SUBSTITUTION_LIFT_CACHE "+JSON.stringify(summary));
