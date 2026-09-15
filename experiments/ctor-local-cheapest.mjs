// Prospective separator: constructor-local cheapest-first conversion.
//
// For two raw applications of the exact same verified constructor constant,
// compare fields cheapest-first before any outer evaluation. A retained REJECT
// on one field is a sound negative consequence by constructor injectivity.
// UNKNOWN/host-stack only decline the shortcut and roll back completely.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

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

const proto=K.Kernel.prototype, retained=proto.equal;
const CAP=50000;

function rawSpine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse();
  return {head:e,args};
}
function cheapPair(a,b){
  if(a===b) return -1000000;
  if(!Array.isArray(a)||!Array.isArray(b)) return -10000;
  if(a[0]!==b[0]) return -100000;
  if(["const","var","nat","strlit","sort"].includes(a[0])) return -50000;
  let score=0,stack=[a,b],seen=new Set();
  while(stack.length&&score<256){
    const x=stack.pop();
    if(!Array.isArray(x)||seen.has(x)) continue;
    seen.add(x); score++;
    for(let i=1;i<x.length;i++) if(Array.isArray(x[i])) stack.push(x[i]);
  }
  return score;
}
function install(enabled){
  proto.equal=retained;
  if(!enabled) return;
  proto.equal=function(a,b,ctx=[]){
    if(this.localDefs || (this._ctorLocalDepth??0)>0)
      return retained.call(this,a,b,ctx);
    if(this.same(a,b)) return;

    const sa=rawSpine(a),sb=rawSpine(b);
    const sameHead=sa.args.length>0 && sa.args.length===sb.args.length &&
      (sa.head===sb.head || this.same(sa.head,sb.head));
    const d=sameHead&&sa.head?.[0]==="const"?this.env.get(sa.head[1]):null;
    if(!sameHead || d?.kind!=="ctor")
      return retained.call(this,a,b,ctx);

    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    this.budget=Math.min(this.budget,this.steps+CAP);
    this._ctorLocalDepth=1;
    const order=sa.args.map((_,i)=>i)
      .sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));

    try{
      for(const i of order) retained.call(this,sa.args[i],sb.args[i],ctx);
      this._ctorLocalDepth=0;
      this.budget=snap.budget;
      return;
    }catch(e){
      this._ctorLocalDepth=0;
      this.budget=snap.budget;
      if(e instanceof Stop && e.status===K.REJECT) throw e;
      if(!(e instanceof Stop || e instanceof RangeError)) throw e;
      this.steps=snap.steps;
      this.conversionFrontier=snap.frontier;
      return retained.call(this,a,b,ctx);
    }
  };
}

const budget=1_000_000;
function evaluate(mode,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const wrongCases=[];
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected){
      wrong++;
      wrongCases.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null});
    }
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode,counts,wrong,wrongCases,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false);
const candidate=evaluate("ctor-local-cheapest",true);
proto.equal=retained;
if(baseline.wrong) throw new Error("baseline wrong");

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
    if(r.status!==r.expected) continue;
    resolved++; if(r.status==="ACCEPT")resolvedAccept++; else resolvedReject++;
    resolvedCases.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }else if(residual.has(r.name)){
    remaining.push({name:r.name,reason:r.reason,steps:r.steps});
  }
}

const summary={arena_sha256:sha,budget,speculation_cap:CAP,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,wrongCases:candidate.wrongCases,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Constructor-local conversion ordering only. Exact same verified constructor heads compare arguments cheapest-first. A retained REJECT on a field propagates by constructor injectivity; UNKNOWN/host-stack rolls back to retained conversion. No new equality or inequality rule is introduced."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/ctor-local-cheapest.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("CTOR_LOCAL_CHEAPEST "+JSON.stringify(summary));
