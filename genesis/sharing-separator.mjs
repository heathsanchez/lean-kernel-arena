// Prospective separator for preserving structural sharing in constructed terms.
// Frozen variants: baseline, hash-cons only, hash-cons+shift memo,
// hash-cons+substitute memo, hash-cons+both memo.
// No semantic rule changes.
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
const originalMake=proto.make, originalShift=proto.shift, originalSubstitute=proto.substitute;

function objectId(kernel,x) {
  kernel.__objectIds ??= new WeakMap();
  kernel.__nextObjectId ??= 1;
  if(!kernel.__objectIds.has(x)) kernel.__objectIds.set(x,kernel.__nextObjectId++);
  return kernel.__objectIds.get(x);
}
function scalarKey(x) {
  if(typeof x==="string") return "s:"+x;
  if(typeof x==="number") return "n:"+x;
  if(typeof x==="boolean") return "b:"+(x?1:0);
  if(x===null) return "null";
  return typeof x+":"+String(x);
}

function install(kind) {
  proto.make=originalMake;
  proto.shift=originalShift;
  proto.substitute=originalSubstitute;

  const cons=kind!=="baseline";
  const memoShift=kind==="cons-shift"||kind==="cons-both";
  const memoSub=kind==="cons-substitute"||kind==="cons-both";

  if(cons) {
    proto.make=function(...xs) {
      this.tick();
      this.__termCons ??= new Map();
      const key=xs.map(x=>Array.isArray(x)?"a:"+objectId(this,x):scalarKey(x)).join("|");
      const old=this.__termCons.get(key);
      if(old!==undefined) return old;
      this.allocations++;
      this.__termCons.set(key,xs);
      objectId(this,xs);
      return xs;
    };
  }
  if(memoShift) {
    const baseShift=proto.shift;
    proto.shift=function(e,amount,cut=0) {
      if(!Array.isArray(e)) return baseShift.call(this,e,amount,cut);
      this.__shiftMemo ??= new WeakMap();
      let m=this.__shiftMemo.get(e);
      if(!m){m=new Map();this.__shiftMemo.set(e,m);}
      const key=amount+"|"+cut;
      if(m.has(key)) return m.get(key);
      const r=baseShift.call(this,e,amount,cut);
      m.set(key,r); return r;
    };
  }
  if(memoSub) {
    const baseSub=proto.substitute;
    proto.substitute=function(e,arg,depth=0) {
      if(!Array.isArray(e)||!Array.isArray(arg)) return baseSub.call(this,e,arg,depth);
      this.__subMemo ??= new WeakMap();
      let byArg=this.__subMemo.get(e);
      if(!byArg){byArg=new WeakMap();this.__subMemo.set(e,byArg);}
      let byDepth=byArg.get(arg);
      if(!byDepth){byDepth=new Map();byArg.set(arg,byDepth);}
      if(byDepth.has(depth)) return byDepth.get(depth);
      const r=baseSub.call(this,e,arg,depth);
      byDepth.set(depth,r); return r;
    };
  }
}

const budget=1_000_000;
function evaluate(kind) {
  install(kind);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null});
  }
  return {kind,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline");
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN"&&["budget-exhausted","host-stack-limit"].includes(r.reason)).map(r=>r.name));
if(residual.size!==19) throw new Error("residual changed: "+residual.size);

const variants=[
  baseline,
  evaluate("cons"),
  evaluate("cons-shift"),
  evaluate("cons-substitute"),
  evaluate("cons-both")
];
proto.make=originalMake;proto.shift=originalShift;proto.substitute=originalSubstitute;

const summaries=[];
for(const v of variants) {
  let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
  const resolvedCases=[],regressions=[];
  for(let i=0;i<rows.length;i++) {
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status) {
      protectedChanged++;
      if(regressions.length<20) regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
    }
    if(residual.has(r.name)&&r.status!=="UNKNOWN") {
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({kind:v.kind,result:r}));
      resolved++;
      if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
    }
  }
  const x={variant:v.kind,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,resolvedAccept,resolvedReject,
    totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,elapsed_ms:v.elapsed_ms,resolvedCases,regressions};
  summaries.push(x);
  console.log("SHARING_VARIANT "+JSON.stringify(x));
}

const lawful=summaries.filter(x=>x.variant!=="baseline"&&x.wrong===0&&x.protectedChanged===0&&x.resolved>0);
lawful.sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps||a.totalConstructed-b.totalConstructed);
const conclusion={
  arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),
  lawful_candidates:lawful.map(x=>x.variant),provisional_winner:lawful[0]?.variant??null,
  claim_boundary:"Prospective representation separator. Hash-consing preserves identity sharing of extensionally identical constructed terms; memoization caches pure structural transforms. Promotion requires integration, ablation, and full replay."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/sharing-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("SHARING_CONCLUSION "+JSON.stringify(conclusion));
