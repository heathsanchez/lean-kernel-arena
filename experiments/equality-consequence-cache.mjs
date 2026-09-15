// Prospective exact positive equality consequence reuse.
//
// A successful definitional-equality proof for the exact expression pair under
// the complete exact local context and capability set is a verified consequence.
// Reuse it without repaying semantic work. Failures, UNKNOWN, REJECT and thrown
// exceptions are never cached.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==188)throw new Error("Arena row count changed");

const proto=K.Kernel.prototype,retainedRun=proto.run,retainedEqual=proto.equal;
function objectId(k,x){
  k.__eqIds??=new WeakMap();k.__eqNextId??=1;
  let id=k.__eqIds.get(x);
  if(id!==undefined)return id;
  id=k.__eqNextId++;k.__eqIds.set(x,id);return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length)return "";
  return ctx.map(x=>(x!==null&&(typeof x==="object"||typeof x==="function"))
    ?"o"+objectId(k,x):typeof x+":"+String(x)).join(",");
}
function capsKey(k){return [...(k.caps??[])].sort().join("\u0000");}
function pairMap(k,a,b){
  k.__eqCache??=new WeakMap();
  let byA=k.__eqCache.get(a);
  if(!byA){byA=new WeakMap();k.__eqCache.set(a,byA);}
  let keys=byA.get(b);
  if(!keys){keys=new Set();byA.set(b,keys);}
  return keys;
}
function install(enabled){
  proto.run=retainedRun;proto.equal=retainedEqual;
  if(!enabled)return;
  proto.run=function(...args){
    this.__eqCache=new WeakMap();
    this.__eqIds=new WeakMap();
    this.__eqNextId=1;
    return retainedRun.apply(this,args);
  };
  proto.equal=function(a,b,ctx=[]){
    if(!Array.isArray(a)||!Array.isArray(b))
      return retainedEqual.call(this,a,b,ctx);
    this.__eqCache??=new WeakMap();
    this.__eqIds??=new WeakMap();
    this.__eqNextId??=1;
    const key=(this.localDefs?"L|":"N|")+capsKey(this)+"|"+ctxKey(this,ctx);
    const keys=pairMap(this,a,b);
    if(keys.has(key))return;
    const out=retainedEqual.call(this,a,b,ctx);
    keys.add(key);
    // Equality is symmetric; this only records a successfully verified result.
    pairMap(this,b,a).add(key);
    return out;
  };
}
function evaluate(mode,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const wrongCases=[];
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected){
      wrong++;wrongCases.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null});
    }
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode,counts,wrong,wrongCases,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}
const baseline=evaluate("baseline",false),candidate=evaluate("exact-positive-equality-cache",true);
proto.run=retainedRun;proto.equal=retainedEqual;
if(baseline.wrong)throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){protectedChanged++;regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});}
  if(residual.has(r.name)&&r.status!=="UNKNOWN"&&r.status===r.expected){
    resolved++;resolvedCases.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }else if(residual.has(r.name))remaining.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps});
}
const summary={arena_sha256:sha,budget:1_000_000,
 baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,wrong:candidate.wrong,wrongCases:candidate.wrongCases,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
   protectedChanged,resolved,resolvedCases,regressions,remaining},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
 claim_boundary:"Execution consequence only. Successful exact definitional equality is cached by exact left/right object identity, complete exact local context, local-definition mode and capability set. Failures are never cached. Symmetric reuse records only an already-proven equality."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/equality-consequence-cache.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("EQUALITY_CONSEQUENCE_CACHE "+JSON.stringify(summary));
