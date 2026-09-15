// Prospective separator for semantic reuse after structural sharing.
// Base repair: hash-cons constructed terms. Candidate caches come ONLY from the
// measured post-sharing hotspots: validate, getApp, instantiateDeclaration,
// whnf, normal, substitute. Singles + full bundle are frozen before outcomes.
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
const originals={};
for(const n of ["make","validate","getApp","instantiateDeclaration","whnf","normal","substitute"])
  originals[n]=proto[n];

function objectId(kernel,x){
  kernel.__ids??=new WeakMap(); kernel.__nextId??=1;
  if(!kernel.__ids.has(x)) kernel.__ids.set(x,kernel.__nextId++);
  return kernel.__ids.get(x);
}
function scalarKey(x){
  if(typeof x==="string") return "s:"+x;
  if(typeof x==="number") return "n:"+x;
  if(typeof x==="boolean") return "b:"+(x?1:0);
  if(x===null) return "null";
  return typeof x+":"+String(x);
}
function paramsKey(kernel){ return [...kernel.params].sort().join("\u0000"); }

function reset(){
  for(const [n,f] of Object.entries(originals)) proto[n]=f;
}
function install(cacheNames){
  reset();
  // Always preserve constructed-term sharing in every candidate and baseline.
  proto.make=function(...xs){
    this.tick();
    this.__cons??=new Map();
    const key=xs.map(x=>Array.isArray(x)?"a:"+objectId(this,x):scalarKey(x)).join("|");
    const old=this.__cons.get(key);
    if(old!==undefined) return old;
    this.allocations++;
    this.__cons.set(key,xs); objectId(this,xs); return xs;
  };
  const has=n=>cacheNames.includes(n);

  if(has("validate")){
    const base=proto.validate;
    proto.validate=function(e){
      if(!Array.isArray(e)) return base.call(this,e);
      this.__validateMemo??=new WeakMap();
      let keys=this.__validateMemo.get(e);
      const k=paramsKey(this);
      if(keys?.has(k)) return;
      const r=base.call(this,e); // cache successes only
      if(!keys){keys=new Set();this.__validateMemo.set(e,keys);}
      keys.add(k); return r;
    };
  }
  if(has("getApp")){
    const base=proto.getApp;
    proto.getApp=function(e){
      if(!Array.isArray(e)) return base.call(this,e);
      this.__getAppMemo??=new WeakMap();
      if(this.__getAppMemo.has(e)) return this.__getAppMemo.get(e);
      const r=base.call(this,e); this.__getAppMemo.set(e,r); return r;
    };
  }
  if(has("instantiateDeclaration")){
    const base=proto.instantiateDeclaration;
    proto.instantiateDeclaration=function(ref,term){
      if(!Array.isArray(ref)||!Array.isArray(term)) return base.call(this,ref,term);
      this.__instMemo??=new WeakMap();
      let byTerm=this.__instMemo.get(ref);
      if(!byTerm){byTerm=new WeakMap();this.__instMemo.set(ref,byTerm);}
      if(byTerm.has(term)) return byTerm.get(term);
      const r=base.call(this,ref,term); byTerm.set(term,r); return r;
    };
  }
  if(has("whnf")){
    const base=proto.whnf;
    proto.whnf=function(e){
      if(!Array.isArray(e)) return base.call(this,e);
      this.__whnfMemo??=new WeakMap();
      if(this.__whnfMemo.has(e)) return this.__whnfMemo.get(e);
      const r=base.call(this,e); this.__whnfMemo.set(e,r); return r;
    };
  }
  if(has("normal")){
    const base=proto.normal;
    proto.normal=function(e){
      if(!Array.isArray(e)) return base.call(this,e);
      this.__normalMemo??=new WeakMap();
      if(this.__normalMemo.has(e)) return this.__normalMemo.get(e);
      const r=base.call(this,e); this.__normalMemo.set(e,r); return r;
    };
  }
  if(has("substitute")){
    const base=proto.substitute;
    proto.substitute=function(e,arg,depth=0){
      if(!Array.isArray(e)||!Array.isArray(arg)) return base.call(this,e,arg,depth);
      this.__subMemo??=new WeakMap();
      let byArg=this.__subMemo.get(e);
      if(!byArg){byArg=new WeakMap();this.__subMemo.set(e,byArg);}
      let byDepth=byArg.get(arg);
      if(!byDepth){byDepth=new Map();byArg.set(arg,byDepth);}
      if(byDepth.has(depth)) return byDepth.get(depth);
      const r=base.call(this,e,arg,depth); byDepth.set(depth,r); return r;
    };
  }
}

const budget=1_000_000;
function evaluate(name,cacheNames){
  install(cacheNames);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null});
  }
  return {name,cacheNames,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("sharing-only",[]);
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN"&&["budget-exhausted","host-stack-limit"].includes(r.reason)).map(r=>r.name));
if(residual.size!==18) throw new Error("post-sharing residual changed: "+residual.size);

const names=["validate","getApp","instantiateDeclaration","whnf","normal","substitute"];
const variants=[baseline];
for(const n of names) variants.push(evaluate(n,[n]));
variants.push(evaluate("all-hot",names));
reset();

const summaries=[];
for(const v of variants){
  let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
  const resolvedCases=[],regressions=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status){
      protectedChanged++;
      if(regressions.length<20) regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
    }
    if(residual.has(r.name)&&r.status!=="UNKNOWN"){
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({variant:v.name,result:r}));
      resolved++;
      if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
    }
  }
  const s={variant:v.name,caches:v.cacheNames,counts:v.counts,wrong:v.wrong,protectedChanged,
    resolved,resolvedAccept,resolvedReject,totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,
    elapsed_ms:v.elapsed_ms,resolvedCases,regressions};
  summaries.push(s);
  console.log("SEMANTIC_REUSE_VARIANT "+JSON.stringify(s));
}
const lawful=summaries.filter(s=>s.variant!=="sharing-only"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0);
lawful.sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps||a.elapsed_ms-b.elapsed_ms);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),
  lawful_candidates:lawful.map(x=>x.variant),provisional_winner:lawful[0]?.variant??null,
  claim_boundary:"Prospective semantic-reuse separator on top of hash-consing. Caches store only successful deterministic consequences under stable kernel state. Promotion requires ablation and full replay."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/semantic-reuse-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("SEMANTIC_REUSE_CONCLUSION "+JSON.stringify(conclusion));
