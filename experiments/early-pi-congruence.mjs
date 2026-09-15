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

const proto=K.Kernel.prototype,retained=proto.equal;
const stats={eligible:0,success:0,failed:0};

function install(enabled){
  proto.equal=retained;
  if(!enabled) return;
  proto.equal=function(a,b,ctx=[]){
    if(!this.localDefs && Array.isArray(a)&&Array.isArray(b)&&a[0]==="pi"&&b[0]==="pi"){
      stats.eligible++;
      if(a===b || this.same(a,b)){stats.success++;return;}
      try{
        this.equal(a[1],b[1],ctx);
        this.equal(a[2],b[2],[...ctx,a[1]]);
        stats.success++;
        return;
      }catch(e){
        stats.failed++;
        throw e;
      }
    }
    return retained.call(this,a,b,ctx);
  };
}

function evaluate(mode,enabled,subset=rows){
  install(enabled);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]++;totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,
    stats:{eligible:stats.eligible-before.eligible,success:stats.success-before.success,failed:stats.failed-before.failed},results};
}

const focusRows=rows.filter(r=>r.name.endsWith("good/perf/fueled-chain.ndjson"));
const focusBase=evaluate("focus-baseline",false,focusRows);
const focus=evaluate("focus-candidate",true,focusRows);
console.log("EARLY_PI_CONGRUENCE_FOCUS "+JSON.stringify({baseline:focusBase,candidate:focus}));
if(focus.wrong)throw new Error("focus wrong");

const baseline=evaluate("baseline",false),candidate=evaluate("candidate",true);install(false);
if(baseline.wrong||candidate.wrong)throw new Error("wrong verdict");
let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});}
  if(b.status==="UNKNOWN"){
    if(c.status!=="UNKNOWN"&&c.status===c.expected)resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
    else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,frontier_declaration:c.frontier_declaration});
  }
}
const report={arena_sha256:sha,budget:1_000_000,
 baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
   elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved.length>0,
 claim_boundary:"Execution ordering only. In the ordinary kernel, raw Pi/Pi terms are already WHNF type formers, so definitional equality may use the retained Pi congruence rule immediately: domains equal in the current context and codomains equal under the left domain binder. No proof, eta, unit, or structure rule is bypassed for values because a Pi expression is itself a type, not a proof/value."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/early-pi-congruence.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("EARLY_PI_CONGRUENCE "+JSON.stringify(report));
