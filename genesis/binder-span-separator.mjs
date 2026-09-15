// Prospective separator for consequence-derived binder-span metadata.
// Frozen candidates: none, guard shift, guard substitute, both.
// A term gets one cached structural fact: max(i - localBinderDepth) over bvars.
// If this maximum is below the current cut/depth, shift/substitute is provably identity.
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
const originalShift=proto.shift, originalSubstitute=proto.substitute;

function maxFreeRelative(kernel,e) {
  if(!Array.isArray(e)) return -Infinity;
  kernel.__maxFreeMemo ??= new WeakMap();
  if(kernel.__maxFreeMemo.has(e)) return kernel.__maxFreeMemo.get(e);

  // Compute max raw index minus binders introduced between root and occurrence.
  // Charge traversal on first encounter; subsequent lookups are compiled metadata reuse.
  function walk(x,binders) {
    kernel.tick();
    switch(x[0]) {
      case "sort": case "const": case "nat": case "strlit": return -Infinity;
      case "var": return x[1]-binders;
      case "pi": case "lam":
        return Math.max(walk(x[1],binders),walk(x[2],binders+1));
      case "app":
        return Math.max(walk(x[1],binders),walk(x[2],binders));
      case "proj":
        return walk(x[3],binders);
      case "let":
        return Math.max(walk(x[1],binders),walk(x[2],binders),walk(x[3],binders+1));
      default:
        return Infinity; // never authorize skipping unknown syntax
    }
  }
  const m=walk(e,0);
  kernel.__maxFreeMemo.set(e,m);
  return m;
}

function installVariant(name) {
  proto.shift=originalShift;
  proto.substitute=originalSubstitute;

  if(name==="shift" || name==="both") {
    proto.shift=function(e,amount,cut=0) {
      // If no occurrence can satisfy i >= cut + localBinderDepth, shift is identity.
      if(Array.isArray(e) && maxFreeRelative(this,e)<cut) return e;
      return originalShift.call(this,e,amount,cut);
    };
  }
  if(name==="substitute" || name==="both") {
    proto.substitute=function(e,arg,depth=0) {
      // Substitution changes only occurrences with i-localBinderDepth >= depth:
      // equality gets replaced; greater indices get decremented.
      if(Array.isArray(e) && maxFreeRelative(this,e)<depth) return e;
      return originalSubstitute.call(this,e,arg,depth);
    };
  }
}

const budget=1_000_000;
function evaluate(name) {
  installVariant(name);
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

const baseline=evaluate("none");
if(baseline.wrong) throw new Error("baseline wrong");
const residualNames=new Set(baseline.results.filter(r=>r.status==="UNKNOWN"&&["budget-exhausted","host-stack-limit"].includes(r.reason)).map(r=>r.name));
if(residualNames.size!==19) throw new Error("residual changed: "+residualNames.size);
const variants=[baseline,evaluate("shift"),evaluate("substitute"),evaluate("both")];
proto.shift=originalShift; proto.substitute=originalSubstitute;

const summaries=[];
for(const v of variants) {
  let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
  const resolvedCases=[],regressions=[];
  for(let i=0;i<rows.length;i++) {
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status) {
      protectedChanged++;
      if(regressions.length<10) regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
    }
    if(residualNames.has(r.name)&&r.status!=="UNKNOWN") {
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({variant:v.name,result:r}));
      resolved++;
      if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,steps:r.steps});
    }
  }
  const summary={variant:v.name,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,resolvedAccept,resolvedReject,
    totalSteps:v.totalSteps,elapsed_ms:v.elapsed_ms,resolvedCases,regressions};
  summaries.push(summary);
  console.log("BINDER_SPAN_VARIANT "+JSON.stringify(summary));
}

const lawful=summaries.filter(s=>s.variant!=="none"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0);
lawful.sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps||a.elapsed_ms-b.elapsed_ms);
const winner=lawful[0]??null;
const conclusion={
  arena_sha256:sha,budget,
  baseline:summaries.find(s=>s.variant==="none"),
  candidates:summaries.filter(s=>s.variant!=="none"),
  lawful_candidates:lawful.map(s=>s.variant),
  provisional_winner:winner?.variant??null,
  claim_boundary:"Prospective representation/execution separator. Metadata is derived from term structure and authorizes only transformations proven to be identity. Promotion requires integration, ablation, protected replay."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/binder-span-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("BINDER_SPAN_CONCLUSION "+JSON.stringify(conclusion));
