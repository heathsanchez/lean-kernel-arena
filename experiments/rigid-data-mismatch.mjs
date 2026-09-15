// Separator: reject only a rigid constructor disagreement that is already
// present before normalization. No reducible head is treated as injective.
// A direct mismatch is certified only for distinct constructors of the same
// monomorphic non-Prop inductive.
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
const originalEqual=proto.equal;

function rawApp(kernel,e){
  const args=[]; let h=e;
  while(Array.isArray(h)&&h[0]==="app"){
    kernel.tick();
    args.push(h[2]); h=h[1];
  }
  args.reverse();
  return [h,args];
}
function nonPropMonoInd(kernel,indName){
  const ind=kernel.env?.get(indName);
  return ind?.kind==="inductive" &&
    (ind.levelParams?.length??0)===0 &&
    ind.isProp===false;
}
function directCtorMismatch(kernel,a,b){
  const [ha,aa]=rawApp(kernel,a),[hb,ab]=rawApp(kernel,b);
  if(ha?.[0]!=="const"||hb?.[0]!=="const"||ha[1]===hb[1]) return false;
  const da=kernel.env?.get(ha[1]),db=kernel.env?.get(hb[1]);
  return da?.kind==="ctor" && db?.kind==="ctor" &&
    da.induct===db.induct && nonPropMonoInd(kernel,da.induct);
}
function rigidPathMismatch(kernel,a,b,seen=new WeakMap()){
  kernel.tick();
  if(a===b||!Array.isArray(a)||!Array.isArray(b)) return false;
  if(directCtorMismatch(kernel,a,b)) return true;

  let sb=seen.get(a);
  if(sb?.has(b)) return false;
  if(!sb){sb=new WeakSet();seen.set(a,sb);}
  sb.add(b);

  const [ha,aa]=rawApp(kernel,a),[hb,ab]=rawApp(kernel,b);
  if(ha?.[0]!=="const"||hb?.[0]!=="const"||ha[1]!==hb[1]||aa.length!==ab.length) return false;
  const d=kernel.env?.get(ha[1]);
  let rigid=false;
  if(d?.kind==="inductive") rigid=true; // a type former: its arguments are conversion-relevant
  else if(d?.kind==="ctor" && nonPropMonoInd(kernel,d.induct)) rigid=true;
  if(!rigid) return false;

  // Any certified mismatch in a conversion-relevant argument certifies the whole.
  for(let i=0;i<aa.length;i++) if(rigidPathMismatch(kernel,aa[i],ab[i],seen)) return true;
  return false;
}

function install(enabled){
  proto.equal=originalEqual;
  if(!enabled) return;
  proto.equal=function(a,b,ctx=[]){
    if(this.caps.has("rigid-conversion") && rigidPathMismatch(this,a,b))
      this.reject("rigid-data-constructor-mismatch");
    return originalEqual.call(this,a,b,ctx);
  };
}

const budget=1_000_000;
function evaluate(name,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,fallback_mode:r.fallback_mode??null});
  }
  return {name,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false);
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
const candidate=evaluate("rigid-data-mismatch",true);
proto.equal=originalEqual;

let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++;
    regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)){
    if(r.status!=="UNKNOWN"){
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
      resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed});
    } else remaining.push({name:r.name,reason:r.reason,steps:r.steps});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  claim_boundary:"Prospective negative consequence only. Descends solely through rigid inductive type-former applications and monomorphic non-Prop constructor applications; rejects only on distinct constructors of the same monomorphic non-Prop inductive. Reducible heads and Prop constructors are never used as separators."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/rigid-data-mismatch.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("RIGID_DATA_MISMATCH "+JSON.stringify(summary));
