// Prospective separator: cache successful validation at the actual iterative
// subtree boundary. The retained stack-safe validator no longer calls
// this.validate recursively, so wrapper memoization cannot see shared children.
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
const retainedRun=proto.run, retainedValidate=proto.validate;
function paramsKey(k){return [...(k.params??[])].sort().join("\u0000");}
function slot(k,e,key){
  if(!Array.isArray(e)) return null;
  k.__validationDag ??= new WeakMap();
  let s=k.__validationDag.get(e);
  if(!(s instanceof Set)){s=new Set();k.__validationDag.set(e,s);}
  return {has:()=>s.has(key),set:()=>s.add(key)};
}
function install(mode){
  proto.run=retainedRun; proto.validate=retainedValidate;
  if(mode==="baseline") return;
  proto.run=function(...args){
    this.__validationDag=new WeakMap();
    return retainedRun.apply(this,args);
  };
  proto.validate=function(root){
    const key=paramsKey(this),work=[{kind:"visit",e:root}];
    while(work.length){
      const f=work.pop(),e=f.e;
      const s=slot(this,e,key);
      if(f.kind==="done"){s?.set();continue;}
      if(s?.has()){if(mode==="tick")this.tick();continue;}

      if(Array.isArray(e)&&["sort","var","const","nat","strlit"].includes(e[0])){
        retainedValidate.call(this,e);
        s?.set();
        continue;
      }

      this.tick();
      if(!Array.isArray(e)||typeof e[0]!=="string")this.reject("malformed-term");
      const arities={sort:2,var:2,const:2,nat:2,strlit:2,proj:4,pi:3,lam:3,app:3,let:4};
      if(!(e[0] in arities))this.unknown("syntax:"+e[0]);
      if(e.length!==arities[e[0]]&&!(e[0]==="const"&&e.length===3))this.reject("malformed-arity");

      work.push({kind:"done",e});
      if(e[0]==="proj"){
        this.need("projections");
        if(typeof e[1]!=="string"||!Number.isSafeInteger(e[2])||e[2]<0)this.reject("malformed-projection");
        work.push({kind:"visit",e:e[3]});
      }else{
        for(let i=e.length-1;i>=1;i--)work.push({kind:"visit",e:e[i]});
      }
    }
  };
}

const budget=1_000_000;
function evaluate(mode){
  install(mode);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,fallback_mode:r.fallback_mode??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}
const variants=["baseline","tick","free"].map(evaluate);
proto.run=retainedRun;proto.validate=retainedValidate;
const baseline=variants[0];
if(baseline.wrong)throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
const summaries=[];
for(const v of variants){
  let protectedChanged=0,resolved=0;const resolvedCases=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status){protectedChanged++;regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});}
    if(residual.has(r.name)){
      if(r.status!=="UNKNOWN"){
        if(r.status!==r.expected)throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
        resolved++;resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
      }else remaining.push({name:r.name,reason:r.reason,steps:r.steps});
    }
  }
  const s={mode:v.mode,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,totalSteps:v.totalSteps,totalConstructed:v.totalConstructed,elapsed_ms:v.elapsed_ms,resolvedCases,regressions,remaining};
  summaries.push(s);console.log("VALIDATION_DAG_VARIANT "+JSON.stringify(s));
}
const lawful=summaries.filter(s=>s.mode!=="baseline"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0)
  .sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),lawful_candidates:lawful.map(x=>x.mode),provisional_winner:lawful[0]?.mode??null,
  claim_boundary:"Execution compilation only. Successful subtree validation is reused for the exact term identity plus complete universe-parameter set inside the retained iterative validator. No malformed or failed validation is cached."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/validation-dag-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("VALIDATION_DAG_CONCLUSION "+JSON.stringify(conclusion));
