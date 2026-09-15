// Prospective local-definition context repair.
// Base present: hash-consing + normal-form reuse (the two independently earned
// representation optimizations). Candidate keeps let definitions in local context
// and unfolds them on demand during conversion instead of substituting the whole body.
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
for(const n of ["make","normal","infer","whnf","equal","sortOf"]) originals[n]=proto[n];

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
function reset(){ for(const [n,f] of Object.entries(originals)) proto[n]=f; }

function installBase(){
  reset();
  proto.make=function(...xs){
    this.tick(); this.__cons??=new Map();
    const key=xs.map(x=>Array.isArray(x)?"a:"+objectId(this,x):scalarKey(x)).join("|");
    const old=this.__cons.get(key);
    if(old!==undefined) return old;
    this.allocations++; this.__cons.set(key,xs); objectId(this,xs); return xs;
  };
  const baseNormal=originals.normal;
  proto.normal=function(e){
    if(!Array.isArray(e)) return baseNormal.call(this,e);
    this.__normalMemo??=new WeakMap();
    let byCtx=this.__normalMemo.get(e);
    if(!byCtx){byCtx=new Map();this.__normalMemo.set(e,byCtx);}
    const ctx=this.__activeCtx??[];
    const key=ctx.map(entry=>{
      if(entry?.__localDef===true)
        return "d:"+objectId(this,entry.type)+":"+objectId(this,entry.value);
      return Array.isArray(entry)?"t:"+objectId(this,entry):"x:"+String(entry);
    }).join(",");
    if(byCtx.has(key)) return byCtx.get(key);
    const r=baseNormal.call(this,e); byCtx.set(key,r); return r;
  };
}

function withCtx(kernel,ctx,fn){
  const old=kernel.__activeCtx;
  kernel.__activeCtx=ctx;
  try{return fn();} finally{kernel.__activeCtx=old;}
}

function installLocalDefs(){
  installBase();

  const baseInfer=originals.infer;
  const baseWhnf=originals.whnf;
  const baseEqual=originals.equal;
  const baseSortOf=originals.sortOf;

  proto.infer=function(e,ctx){
    return withCtx(this,ctx,()=>{
      if(e[0]==="var"){
        this.tick(); this.need("binders");
        if(e[1]>=ctx.length) this.reject("unbound-variable");
        const entry=ctx[ctx.length-1-e[1]];
        const ty=entry?.__localDef===true?entry.type:entry;
        return this.shift(ty,e[1]+1);
      }
      if(e[0]==="let"){
        this.tick(); this.need("reduction");
        this.sortOf(e[1],ctx);
        this.equal(this.infer(e[2],ctx),e[1],ctx);
        const entry={__localDef:true,type:e[1],value:e[2]};
        const bodyType=this.infer(e[3],[...ctx,entry]);
        // Result type leaves the let scope. Only the result type is instantiated;
        // the body itself was never copied.
        return this.substitute(bodyType,e[2]);
      }
      return baseInfer.call(this,e,ctx);
    });
  };

  proto.whnf=function(e){
    const ctx=this.__activeCtx??[];
    if(Array.isArray(e)&&e[0]==="var"&&e[1]<ctx.length){
      const entry=ctx[ctx.length-1-e[1]];
      if(entry?.__localDef===true){
        this.tick(); this.need("reduction");
        // Keep the local-definition slot in the dynamic context while unfolding:
        // lift the value across the let binder itself plus any inner binders.
        return this.whnf(this.shift(entry.value,e[1]+1));
      }
    }
    return baseWhnf.call(this,e);
  };

  proto.equal=function(a,b,ctx=[]){
    return withCtx(this,ctx,()=>baseEqual.call(this,a,b,ctx));
  };
  proto.sortOf=function(e,ctx){
    return withCtx(this,ctx,()=>baseSortOf.call(this,e,ctx));
  };
}

const budget=1_000_000;

function runRow(row,useLocalDefs){
  useLocalDefs?installLocalDefs():installBase();
  return K.checkExport(row.input,caps,budget);
}
function evaluate(name,useLocalDefs){
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=runRow(row,useLocalDefs);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {name,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}
function evaluateFallback(){
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0,fallbackRuns=0,conflicts=0;
  const t0=Date.now();
  for(const row of rows){
    const base=runRow(row,false);
    let chosen=base,alt=null;
    if(base.status==="UNKNOWN"){
      fallbackRuns++;
      alt=runRow(row,true);
      if(alt.status!=="UNKNOWN") chosen=alt;
    }
    if(base.status!=="UNKNOWN"&&alt!==null&&alt.status!=="UNKNOWN"&&base.status!==alt.status) conflicts++;
    counts[chosen.status]=(counts[chosen.status]??0)+1;
    totalSteps+=(base.steps??0)+(alt?.steps??0);
    totalConstructed+=(base.constructed??0)+(alt?.constructed??0);
    if(chosen.status!=="UNKNOWN"&&chosen.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:chosen.status,reason:chosen.reason,
      base_status:base.status,base_reason:base.reason,
      fallback_status:alt?.status??null,fallback_reason:alt?.reason??null,
      steps:(base.steps??0)+(alt?.steps??0),constructed:(base.constructed??0)+(alt?.constructed??0)});
  }
  return {name:"baseline-first-local-def-fallback",counts,wrong,totalSteps,totalConstructed,
    elapsed_ms:Date.now()-t0,fallbackRuns,conflicts,results};
}

const baseline=evaluate("retained",false);
if(baseline.wrong) throw new Error("baseline wrong");
const candidate=evaluate("local-def-context",true);
if(candidate.wrong) throw new Error("candidate wrong");
const portfolio=evaluateFallback();
reset();

const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=portfolio.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status) protectedChanged++;
  if(residual.has(r.name)){
    if(r.status!=="UNKNOWN"){
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
      resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
    } else remaining.push({name:r.name,reason:r.reason});
  }
}
const standaloneRegressions=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status)
    standaloneRegressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,
    totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,
    totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    standaloneRegressions},
  portfolio:{counts:portfolio.counts,wrong:portfolio.wrong,totalSteps:portfolio.totalSteps,
    totalConstructed:portfolio.totalConstructed,elapsed_ms:portfolio.elapsed_ms,
    fallbackRuns:portfolio.fallbackRuns,conflicts:portfolio.conflicts,protectedChanged,
    resolved,resolvedAccept,resolvedReject,resolvedCases,remaining},
  lawful:portfolio.wrong===0&&protectedChanged===0&&portfolio.conflicts===0,
  promotable:portfolio.wrong===0&&protectedChanged===0&&portfolio.conflicts===0&&resolved>0,
  claim_boundary:"Default-stack portfolio separator. The retained checker has first refusal. The exact local-definition procedure is invoked only after retained UNKNOWN; existing ACCEPT/REJECT verdicts therefore cannot be weakened. Promotion still requires treating the local-definition procedure itself as an independently sound exact checker, plus ablation and replay."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/local-def-fallback.json",import.meta.url),JSON.stringify({summary,baseline,candidate,portfolio},null,2));
console.log("LOCAL_DEF_FALLBACK "+JSON.stringify(summary));
