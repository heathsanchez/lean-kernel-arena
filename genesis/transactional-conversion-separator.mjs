// Prospective conversion-planning separator. Revisit two sufficient-condition
// probes previously ablated because failed probes consumed the later fallback's
// semantic budget. Here failures are transactional: budget/frontier are restored.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "./kernel.mjs";
import {Stop} from "./kernel-base.mjs";

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

const proto=K.Kernel.prototype, retained=proto.equal;
function probe(kernel,fn){
  const steps=kernel.steps,frontier=kernel.conversionFrontier;
  try { fn(); return true; }
  catch(e){
    if(!(e instanceof Stop)) throw e;
    kernel.steps=steps;
    kernel.conversionFrontier=frontier;
    return false;
  }
}
function install(mode){
  proto.equal=retained;
  if(!mode) return;
  proto.equal=function(a,b,ctx=[]){
    if(this.same(a,b)) return;

    if(mode.includes("P")&&this.caps.has("proof-irrelevance")){
      const ok=probe(this,()=>{
        const ta=this.proofType(a,ctx),tb=this.proofType(b,ctx);
        if(ta===null||tb===null) throw new Stop(K.UNKNOWN,"probe-not-proofs");
        retained.call(this,ta,tb,ctx);
      });
      if(ok) return;
    }

    if(mode.includes("C")&&a?.[0]==="app"&&b?.[0]==="app"&&this.same(a[1],b[1])){
      const ok=probe(this,()=>retained.call(this,a[2],b[2],ctx));
      if(ok) return;
    }
    return retained.call(this,a,b,ctx);
  };
}
const budget=1_000_000;
function evaluate(mode){
  install(mode);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};let wrong=0,totalSteps=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget); counts[r.status]=(counts[r.status]??0)+1; totalSteps+=r.steps??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode:mode||"none",counts,wrong,totalSteps,elapsed_ms:Date.now()-t0,results};
}
const variants=[evaluate(""),evaluate("P"),evaluate("C"),evaluate("PC")]; proto.equal=retained;
const baseline=variants[0]; if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
const summaries=[];
for(const v of variants){
  let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
  const resolvedCases=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status){protectedChanged++;regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});}
    if(residual.has(r.name)){
      if(r.status!=="UNKNOWN"){
        if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({mode:v.mode,result:r}));
        resolved++;if(r.status==="ACCEPT")resolvedAccept++;else resolvedReject++;
        resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
      }else remaining.push({name:r.name,reason:r.reason});
    }
  }
  const s={mode:v.mode,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,resolvedAccept,resolvedReject,totalSteps:v.totalSteps,elapsed_ms:v.elapsed_ms,resolvedCases,remaining,regressions};
  summaries.push(s);console.log("TRANSACTIONAL_CONVERSION_VARIANT "+JSON.stringify(s));
}
const lawful=summaries.filter(s=>s.mode!=="none"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0)
  .sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),
  lawful_candidates:lawful.map(x=>x.mode),provisional_winner:lawful[0]?.mode??null,
  claim_boundary:"Only sufficient conditions may return success. Any failed speculative proof restores consumed semantic steps and the diagnostic frontier before delegating to retained conversion."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/transactional-conversion-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("TRANSACTIONAL_CONVERSION_CONCLUSION "+JSON.stringify(conclusion));
