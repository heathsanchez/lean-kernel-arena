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
    const traceThis=e[0]==="var"&&e[1]===3&&ctx.length===7;
    if(byCtx.has(key)) {
      if(traceThis) (this.__localTrace??=[]).push({where:"normal",event:"hit",index:3,ctxlen:7,result:JSON.stringify(byCtx.get(key)).slice(0,500)});
      return byCtx.get(key);
    }
    if(traceThis) (this.__localTrace??=[]).push({where:"normal",event:"miss",index:3,ctxlen:7});
    const r=baseNormal.call(this,e);
    if(traceThis) (this.__localTrace??=[]).push({where:"normal",event:"store",index:3,ctxlen:7,result:JSON.stringify(r).slice(0,500)});
    byCtx.set(key,r); return r;
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
      if(e[1]===3&&ctx.length===7)
        (this.__localTrace??=[]).push({where:"whnf",index:3,ctxlen:7,kind:entry?.__localDef===true?"local-def":"binder"});
      if(entry?.__localDef===true){
        this.tick(); this.need("reduction");
        const lifted=this.shift(entry.value,e[1]+1);
        if(e[1]===3&&ctx.length===7)
          (this.__localTrace??=[]).push({where:"whnf",event:"unfold",shift:e[1]+1,lifted:JSON.stringify(lifted).slice(0,500)});
        // Keep the local-definition slot in the dynamic context while unfolding.
        return this.whnf(lifted);
      }
    }
    return baseWhnf.call(this,e);
  };

  proto.equal=function(a,b,ctx=[]){
    return withCtx(this,ctx,()=>{
      try { return baseEqual.call(this,a,b,ctx); }
      catch(e) {
        if(e instanceof K.Stop && e.status===K.UNKNOWN && e.message==="conversion-frontier" &&
           this.conversionFrontier && this.conversionFrontier.context===undefined) {
          this.conversionFrontier.local_trace = (this.__localTrace??[]).slice(-40);
          this.conversionFrontier.context = ctx.map((entry,i)=>({
            slot:i,
            from_top:ctx.length-1-i,
            kind:entry?.__localDef===true?"local-def":"binder",
            type:entry?.__localDef===true?JSON.stringify(entry.type).slice(0,500):JSON.stringify(entry).slice(0,500),
            value:entry?.__localDef===true?JSON.stringify(entry.value).slice(0,500):null
          }));
        }
        throw e;
      }
    });
  };
  proto.sortOf=function(e,ctx){
    return withCtx(this,ctx,()=>baseSortOf.call(this,e,ctx));
  };
}

const budget=1_000_000;
function evaluate(name,useLocalDefs){
  useLocalDefs?installLocalDefs():installBase();
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null,
      conversion_frontier:r.conversion_frontier??null,frontier_declaration:r.frontier_declaration??null});
  }
  return {name,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("sharing+normal",false);
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN"&&["budget-exhausted","host-stack-limit"].includes(r.reason)).map(r=>r.name));
if(residual.size!==17) throw new Error("baseline residual changed: "+residual.size);

const candidate=evaluate("local-def-context",true);
reset();

let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++;
    regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason,
      conversion_frontier:r.conversion_frontier??null,frontier_declaration:r.frontier_declaration??null});
  }
  if(residual.has(r.name)&&r.status!=="UNKNOWN"){
    if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
    resolved++;
    if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
    resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
    elapsed_ms:candidate.elapsed_ms,protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions},
  lawful:candidate.wrong===0&&protectedChanged===0,
  claim_boundary:"Prospective local-state representation repair. Let values are retained in context and unfolded on demand; only the final inferred type is instantiated when leaving let scope. No Lean semantic rule added."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/local-def-context.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("LOCAL_DEF_CONTEXT "+JSON.stringify(summary));
