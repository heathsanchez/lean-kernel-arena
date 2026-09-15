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
const retained={run:proto.run,shift:proto.shift,substitute:proto.substitute};
let banks=new WeakMap();
const stats={runs:0,shiftQ:0,shiftH:0,shiftCross:0,substQ:0,substH:0,substCross:0};

function ensureBank(decls){
  let b=banks.get(decls);
  if(!b){b={serial:0,shift:new WeakMap(),subst:new WeakMap()};banks.set(decls,b);}
  return b;
}
function shiftSlot(bank,e){
  let m=bank.shift.get(e);if(!m){m=new Map();bank.shift.set(e,m);}return m;
}
function substSlot(bank,e,arg){
  let by=bank.subst.get(e);if(!by){by=new WeakMap();bank.subst.set(e,by);}
  let m=by.get(arg);if(!m){m=new Map();by.set(arg,m);}return m;
}
function reset(){
  proto.run=retained.run; proto.shift=retained.shift; proto.substitute=retained.substitute;
  banks=new WeakMap();
}
function install(){
  reset();
  proto.run=function(term,expected,declarations=[],parameters=[]){
    const bank=ensureBank(declarations);
    bank.serial++;
    this.__fallbackTransformBank=bank;
    this.__fallbackTransformOrdinal=bank.serial;
    stats.runs++;
    return retained.run.call(this,term,expected,declarations,parameters);
  };
  proto.shift=function(e,amount,cut=0){
    const bank=this.__fallbackTransformBank;
    if(!bank||!Array.isArray(e)) return retained.shift.call(this,e,amount,cut);
    stats.shiftQ++;
    const key=amount+":"+cut,m=shiftSlot(bank,e);
    if(m.has(key)){
      const hit=m.get(key);stats.shiftH++;if(hit.origin!==this.__fallbackTransformOrdinal)stats.shiftCross++;
      return hit.value;
    }
    const out=retained.shift.call(this,e,amount,cut);
    m.set(key,{value:out,origin:this.__fallbackTransformOrdinal});
    return out;
  };
  proto.substitute=function(e,arg,depth=0){
    const bank=this.__fallbackTransformBank;
    if(!bank||!Array.isArray(e)||!Array.isArray(arg)) return retained.substitute.call(this,e,arg,depth);
    stats.substQ++;
    const m=substSlot(bank,e,arg);
    if(m.has(depth)){
      const hit=m.get(depth);stats.substH++;if(hit.origin!==this.__fallbackTransformOrdinal)stats.substCross++;
      return hit.value;
    }
    const out=retained.substitute.call(this,e,arg,depth);
    m.set(depth,{value:out,origin:this.__fallbackTransformOrdinal});
    return out;
  };
}

function evaluate(mode,useCandidate){
  useCandidate?install():reset();
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]++;totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,fallback_mode:r.fallback_mode??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,fallback_attempt_steps:r.fallback_attempt_steps??null,
      frontier_declaration:r.frontier_declaration??null});
  }
  const delta=Object.fromEntries(Object.keys(stats).map(k=>[k,stats[k]-before[k]]));
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:delta,results};
}

// Candidate first: it receives no warmed baseline process.
const candidate=evaluate("candidate",true);
const baseline=evaluate("baseline",false);
reset();
if(candidate.wrong||baseline.wrong)throw new Error("wrong verdict");

let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});}
  if(b.status==="UNKNOWN"&&c.status!=="UNKNOWN"){
    if(c.status!==c.expected)throw new Error("WRONG_RESOLUTION "+JSON.stringify(c));
    resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed,fallback_mode:c.fallback_mode});
  }else if(b.status==="UNKNOWN")remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,fallback_attempt_reason:c.fallback_attempt_reason});
}
const summary={arena_sha256:sha,budget:1_000_000,
 baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
   stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved.length>0,
 claim_boundary:"Transfer only exact completed pure de-Bruijn transform consequences across retained/stack-safe/LocalDef kernel instances within one parsed checkExport judgment. Keys are immutable expression identity plus exact argument identity and numeric amount/cut/depth. No failures, verdicts, environment-dependent inference, reduction, or conversion results are shared."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/fallback-transform-transfer.json",import.meta.url),JSON.stringify(summary,null,2)+"\n");
console.log("FALLBACK_TRANSFORM_TRANSFER "+JSON.stringify(summary));
