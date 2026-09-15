// Prospective composition: memoize successful inference inside the explicit
// LocalDef continuation machine itself. Nested DAG nodes owned by the machine
// otherwise never cross Kernel.infer and cannot benefit from consequence reuse.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
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
if(rows.length!==188) throw new Error("Arena row count changed");

const proto=K.Kernel.prototype;
const retainedRun=proto.run, retainedInfer=proto.infer;

function objectId(k,x){
  k.__machineCtxIds ??= new WeakMap();
  k.__machineNextId ??= 1;
  let id=k.__machineCtxIds.get(x);
  if(id!==undefined) return id;
  id=k.__machineNextId++;
  k.__machineCtxIds.set(x,id);
  return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length) return "";
  return ctx.map(x=>(x!==null&&(typeof x==="object"||typeof x==="function"))
    ?"o"+objectId(k,x):typeof x+":"+String(x)).join(",");
}
function scoped(k,ctx,fn){
  return typeof k.withCtx==="function" ? k.withCtx(ctx,fn) : fn();
}
function cacheGet(k,e,ctx){
  if(!Array.isArray(e)) return {hit:false,key:null,map:null};
  k.__machineInfer ??= new WeakMap();
  let byCtx=k.__machineInfer.get(e);
  if(!(byCtx instanceof Map)){
    byCtx=new Map();
    k.__machineInfer.set(e,byCtx);
  }
  const key=ctxKey(k,ctx);
  return byCtx.has(key)
    ? {hit:true,value:byCtx.get(key),key,map:byCtx}
    : {hit:false,key,map:byCtx};
}

function memoLocalInfer(root,rootCtx){
  let e=root,ctx=rootCtx,value,returning=false;
  const kont=[];

  while(true){
    if(!returning){
      const memo=cacheGet(this,e,ctx);
      if(memo.hit){
        value=memo.value;
        returning=true;
        continue;
      }
      if(memo.map) kont.push({kind:"memo",map:memo.map,key:memo.key});

      if(Array.isArray(e) && e[0]==="app"){
        this.tick(); this.need("application");
        kont.push({kind:"app-fn",arg:e[2],ctx});
        e=e[1];
        continue;
      }

      if(Array.isArray(e) && e[0]==="lam"){
        this.tick(); this.need("binders");
        scoped(this,ctx,()=>this.sortOf(e[1],ctx));
        kont.push({kind:"lam",domain:e[1],ctx});
        ctx=[...ctx,e[1]];
        e=e[2];
        continue;
      }

      if(Array.isArray(e) && e[0]==="let"){
        this.tick(); this.need("reduction");
        scoped(this,ctx,()=>this.sortOf(e[1],ctx));
        kont.push({kind:"let-value",type:e[1],valueTerm:e[2],body:e[3],ctx});
        e=e[2];
        continue;
      }

      if(Array.isArray(e) && e[0]==="var"){
        this.tick(); this.need("binders");
        if(e[1]>=ctx.length) this.reject("unbound-variable");
        const entry=ctx[ctx.length-1-e[1]];
        const ty=entry?.__localDef===true?entry.type:entry;
        value=this.shift(ty,e[1]+1);
        returning=true;
        continue;
      }

      value=scoped(this,ctx,()=>retainedInfer.call(this,e,ctx));
      returning=true;
      continue;
    }

    if(!kont.length) return value;
    const k=kont.pop();

    if(k.kind==="memo"){
      k.map.set(k.key,value);
      continue;
    }

    if(k.kind==="lam"){
      value=this.make("pi",k.domain,value);
      ctx=k.ctx;
      continue;
    }

    if(k.kind==="app-fn"){
      const fty=scoped(this,k.ctx,()=>this.whnf(value));
      if(fty[0]!=="pi") this.reject("not-a-function");
      kont.push({kind:"app-arg",fty,arg:k.arg,ctx:k.ctx});
      e=k.arg;ctx=k.ctx;returning=false;
      continue;
    }

    if(k.kind==="app-arg"){
      scoped(this,k.ctx,()=>this.equal(value,k.fty[1],k.ctx));
      value=this.substitute(k.fty[2],k.arg);
      ctx=k.ctx;
      continue;
    }

    if(k.kind==="let-value"){
      scoped(this,k.ctx,()=>this.equal(value,k.type,k.ctx));
      const entry={__localDef:true,type:k.type,value:k.valueTerm};
      kont.push({kind:"let-body",valueTerm:k.valueTerm,ctx:k.ctx});
      ctx=[...k.ctx,entry];
      e=k.body;returning=false;
      continue;
    }

    if(k.kind==="let-body"){
      value=this.substitute(value,k.valueTerm);
      ctx=k.ctx;
      continue;
    }

    throw new Error("unknown memo LocalDef continuation frame");
  }
}

function install(enabled){
  proto.run=retainedRun;proto.infer=retainedInfer;
  if(!enabled) return;

  proto.run=function(...args){
    this.__machineInfer=new WeakMap();
    this.__machineCtxIds=new WeakMap();
    this.__machineNextId=1;
    return retainedRun.apply(this,args);
  };

  proto.infer=function(e,ctx=[]){
    if(this.localDefs!==true || !Array.isArray(e) || !["app","lam"].includes(e[0]))
      return retainedInfer.call(this,e,ctx);
    return memoLocalInfer.call(this,e,ctx);
  };
}

const budget=1_000_000;
function evaluate(mode,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      fallback_mode:r.fallback_mode??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false);
const candidate=evaluate("memo-local-machine",true);
proto.run=retainedRun;proto.infer=retainedInfer;
if(baseline.wrong||candidate.wrong) throw new Error("wrong verdict");

const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++;
    regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)&&r.status!=="UNKNOWN"){
    if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
    resolved++; if(r.status==="ACCEPT")resolvedAccept++; else resolvedReject++;
    resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
  }else if(residual.has(r.name)){
    remaining.push({name:r.name,reason:r.reason,steps:r.steps,
      fallback_attempt_reason:r.fallback_attempt_reason,
      fallback_attempt_steps:r.fallback_attempt_steps});
  }
}

const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Execution-only composition. Successful inference is memoized at each exact LocalDef continuation-machine node under the complete exact local context. Failures are never cached; typing, conversion, local-definition and reduction rules are unchanged."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/localdef-machine-memo.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("LOCALDEF_MACHINE_MEMO "+JSON.stringify(summary));
