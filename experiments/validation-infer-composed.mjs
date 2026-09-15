// Prospective composition separator: compile both exact DAG validation and
// exact inference consequences. app-lam is intentionally constructed so either
// repair alone merely exposes the other bottleneck.
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
if(rows.length!==188) throw new Error("Arena row count changed: "+rows.length);

const proto=K.Kernel.prototype;
const retainedRun=proto.run, retainedValidate=proto.validate, retainedInfer=proto.infer;

function objectId(k,x){
  k.__comboIds??=new WeakMap(); k.__comboNextId??=1;
  let id=k.__comboIds.get(x);
  if(id!==undefined) return id;
  id=k.__comboNextId++; k.__comboIds.set(x,id); return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length) return "";
  const parts=new Array(ctx.length);
  for(let i=0;i<ctx.length;i++){
    const x=ctx[i];
    parts[i]=(x!==null&&(typeof x==="object"||typeof x==="function"))
      ?"o"+objectId(k,x):typeof x+":"+String(x);
  }
  return parts.join(",");
}
function paramsKey(k){ return [...(k.params??[])].sort().join("\u0000"); }

function install(candidate){
  proto.run=retainedRun; proto.validate=retainedValidate; proto.infer=retainedInfer;
  if(!candidate) return;

  proto.run=function(...args){
    this.__comboValidation=new WeakMap();
    this.__comboInfer=new WeakMap();
    this.__comboIds=new WeakMap();
    this.__comboNextId=1;
    this.__comboValidationHits=0;
    this.__comboInferHits=0;
    return retainedRun.apply(this,args);
  };

  proto.validate=function(root){
    const key=paramsKey(this), work=[{kind:"visit",e:root}];
    while(work.length){
      const f=work.pop(), e=f.e;
      if(!Array.isArray(e)) return retainedValidate.call(this,e);

      let keys=this.__comboValidation.get(e);
      if(!(keys instanceof Set)){keys=new Set();this.__comboValidation.set(e,keys);}
      if(f.kind==="done"){keys.add(key);continue;}
      if(keys.has(key)){this.__comboValidationHits++;continue;}

      if(["sort","var","const","nat","strlit"].includes(e[0])){
        retainedValidate.call(this,e);
        keys.add(key);
        continue;
      }

      this.tick();
      if(typeof e[0]!=="string") this.reject("malformed-term");
      const arities={sort:2,var:2,const:2,nat:2,strlit:2,proj:4,pi:3,lam:3,app:3,let:4};
      if(!(e[0] in arities)) this.unknown("syntax:"+e[0]);
      if(e.length!==arities[e[0]] && !(e[0]==="const"&&e.length===3)) this.reject("malformed-arity");

      work.push({kind:"done",e});
      if(e[0]==="proj"){
        this.need("projections");
        if(typeof e[1]!=="string"||!Number.isSafeInteger(e[2])||e[2]<0) this.reject("malformed-projection");
        work.push({kind:"visit",e:e[3]});
      }else{
        for(let i=e.length-1;i>=1;i--) work.push({kind:"visit",e:e[i]});
      }
    }
  };

  proto.infer=function(e,ctx=[]){
    if(!Array.isArray(e)) return retainedInfer.call(this,e,ctx);
    let byCtx=this.__comboInfer.get(e);
    if(!(byCtx instanceof Map)){byCtx=new Map();this.__comboInfer.set(e,byCtx);}
    const key=ctxKey(this,ctx);
    if(byCtx.has(key)){this.__comboInferHits++;return byCtx.get(key);}
    const out=retainedInfer.call(this,e,ctx);
    byCtx.set(key,out);
    return out;
  };
}

const budget=1_000_000;
function evaluate(candidate){
  install(candidate);
  const results=[], counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null,
      fallback_mode:r.fallback_mode??null});
  }
  return {candidate,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate(false), candidate=evaluate(true);
proto.run=retainedRun; proto.validate=retainedValidate; proto.infer=retainedInfer;
if(baseline.wrong) throw new Error("baseline wrong");

const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++; regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)&&r.status!=="UNKNOWN"){
    if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
    resolved++; if(r.status==="ACCEPT")resolvedAccept++; else resolvedReject++;
    resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
  }else if(residual.has(r.name)){
    remaining.push({name:r.name,reason:r.reason,steps:r.steps});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Composition of two exact execution consequences only: successful DAG subtree validation by exact identity+universe-parameter set, and successful inference by exact expression identity+complete exact local context. Failures are never cached; no typing, reduction, conversion, or declaration rule changes."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/validation-infer-composed.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("VALIDATION_INFER_COMPOSED "+JSON.stringify(summary));
