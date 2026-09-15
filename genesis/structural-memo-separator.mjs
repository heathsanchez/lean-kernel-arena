// Prospective separator for the hotspot-forced execution repair.
// Candidate family is frozen before outcomes: none, shift memo, substitute memo, both.
// Memoization is per Kernel instance and only caches pure structural transforms.
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

function installVariant(name) {
  proto.shift=originalShift;
  proto.substitute=originalSubstitute;

  if(name==="shift" || name==="both") {
    proto.shift=function(e,amount,cut=0) {
      if(!Array.isArray(e)) return originalShift.call(this,e,amount,cut);
      this.__shiftMemo ??= new WeakMap();
      let m=this.__shiftMemo.get(e);
      if(!m) {m=new Map();this.__shiftMemo.set(e,m);}
      const key=amount+"|"+cut;
      if(m.has(key)) return m.get(key);
      const r=originalShift.call(this,e,amount,cut);
      m.set(key,r);
      return r;
    };
  }

  if(name==="substitute" || name==="both") {
    proto.substitute=function(e,arg,depth=0) {
      if(!Array.isArray(e)||!Array.isArray(arg)) return originalSubstitute.call(this,e,arg,depth);
      this.__substMemo ??= new WeakMap();
      let byArg=this.__substMemo.get(e);
      if(!byArg) {byArg=new WeakMap();this.__substMemo.set(e,byArg);}
      let byDepth=byArg.get(arg);
      if(!byDepth) {byDepth=new Map();byArg.set(arg,byDepth);}
      if(byDepth.has(depth)) return byDepth.get(depth);
      const r=originalSubstitute.call(this,e,arg,depth);
      byDepth.set(depth,r);
      return r;
    };
  }
}

const budget=1_000_000;

function evaluateVariant(name) {
  installVariant(name);
  const results=[];
  const counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0;
  const t0=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;
    if(r.status!=="UNKNOWN" && r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,elapsed_ms:r.elapsed_ms??null});
  }
  return {name,counts,wrong,totalSteps,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluateVariant("none");
if(baseline.wrong!==0) throw new Error("baseline wrong verdicts: "+baseline.wrong);
const residualNames=new Set(baseline.results.filter(r=>r.status==="UNKNOWN"&&["budget-exhausted","host-stack-limit"].includes(r.reason)).map(r=>r.name));
if(residualNames.size!==19) throw new Error("baseline residual changed: "+residualNames.size);

const variants=[baseline];
for(const name of ["shift","substitute","both"]) variants.push(evaluateVariant(name));

// Restore original methods before any final reporting.
proto.shift=originalShift; proto.substitute=originalSubstitute;

const summaries=[];
for(const v of variants) {
  let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
  const regressions=[];
  for(let i=0;i<rows.length;i++) {
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN" && r.status!==b.status) {
      protectedChanged++;
      if(regressions.length<10) regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
    }
    if(residualNames.has(r.name) && r.status!=="UNKNOWN") {
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({variant:v.name,result:r}));
      resolved++;
      if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
    }
  }
  const summary={
    variant:v.name,counts:v.counts,wrong:v.wrong,protectedChanged,
    resolved,resolvedAccept,resolvedReject,totalSteps:v.totalSteps,elapsed_ms:v.elapsed_ms,
    regressions
  };
  summaries.push(summary);
  console.log("STRUCTURAL_MEMO_VARIANT "+JSON.stringify(summary));
}

const lawful=summaries.filter(s=>s.variant!=="none"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0);
lawful.sort((a,b)=>b.resolved-a.resolved || a.totalSteps-b.totalSteps ||
  (a.variant==="both"?1:0)-(b.variant==="both"?1:0));
const winner=lawful[0]??null;
const conclusion={
  arena_sha256:sha,budget,baseline:summaries.find(s=>s.variant==="none"),
  candidates:summaries.filter(s=>s.variant!=="none"),
  lawful_candidates:lawful.map(s=>s.variant),
  provisional_winner:winner?.variant??null,
  claim_boundary:"Prospective execution separator. Memoization changes no kernel semantic rule; promotion still requires explicit ablation and full replay after integration."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/structural-memo-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("STRUCTURAL_MEMO_CONCLUSION "+JSON.stringify(conclusion));
