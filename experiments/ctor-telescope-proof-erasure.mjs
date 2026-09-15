// Prospective constructor-telescope proof irrelevance.
//
// For two fully-applied occurrences of the exact same constructor, classify the
// constructor's own dependent Pi telescope. Data arguments are compared by the
// retained converter in telescope order. An argument whose expected telescope
// domain is proposition-valued is definitionally irrelevant by proof
// irrelevance and is not inspected.
//
// This is a positive equality proof only: same constructor + all data arguments
// equal + proof fields erased. Any failed classification/comparison rolls back
// and delegates to the retained converter unchanged.
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

const proto=K.Kernel.prototype;
const retainedRun=proto.run,retainedEqual=proto.equal;
const CAP=120000;
const stats={eligible:0,classified:0,proofFields:0,proofSkips:0,dataChecks:0,success:0,fallback:0};

function spine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse();
  return {head:e,args};
}
function sameHead(k,a,b){
  return a===b || (Array.isArray(a)&&Array.isArray(b)&&k.same(a,b));
}
function levelKey(u){return JSON.stringify(u??[]);}
function telescopeMask(k,head,ctor,arity){
  k.__ctorProofMask??=new Map();
  const key=ctor.name+"|"+levelKey(head[2])+"|"+arity;
  if(k.__ctorProofMask.has(key)) return k.__ctorProofMask.get(key);

  let ty;
  try{ ty=k.instantiateDeclaration(head,ctor.type); }
  catch(_){ k.__ctorProofMask.set(key,null); return null; }

  const ctx=[],mask=[];
  try{
    for(let i=0;i<arity;i++){
      if(!Array.isArray(ty)||ty[0]!=="pi") ty=k.whnf(ty);
      if(!Array.isArray(ty)||ty[0]!=="pi"){
        k.__ctorProofMask.set(key,null); return null;
      }
      const dom=ty[1];
      const sort=k.sortOf(dom,ctx);
      mask.push(sort===0);
      ctx.push(dom);
      ty=ty[2];
    }
  }catch(_){
    k.__ctorProofMask.set(key,null); return null;
  }
  k.__ctorProofMask.set(key,mask);
  return mask;
}
function install(enabled){
  proto.run=retainedRun;proto.equal=retainedEqual;
  if(!enabled)return;
  proto.run=function(...args){
    this.__ctorProofMask=new Map();
    return retainedRun.apply(this,args);
  };
  proto.equal=function(a,b,ctx=[]){
    if((this._ctorProofEraseDepth??0)>0 ||
       !this.caps.has("proof-irrelevance"))
      return retainedEqual.call(this,a,b,ctx);
    if(this.same(a,b)) return;

    const sa=spine(a),sb=spine(b);
    if(sa.args.length===0 || sa.args.length!==sb.args.length ||
       !sameHead(this,sa.head,sb.head) ||
       !Array.isArray(sa.head)||sa.head[0]!=="const")
      return retainedEqual.call(this,a,b,ctx);

    const ctor=this.env.get(sa.head[1]);
    if(ctor?.kind!=="ctor" ||
       sa.args.length!==(ctor.numParams??0)+(ctor.numFields??0))
      return retainedEqual.call(this,a,b,ctx);

    stats.eligible++;
    const beforeClass=this.steps;
    this._ctorProofEraseDepth=1;
    let mask;
    try{ mask=telescopeMask(this,sa.head,ctor,sa.args.length); }
    finally{ this._ctorProofEraseDepth=0; }
    if(!mask || !mask.some(Boolean)){
      // Classification itself is execution overhead; do not retain it when no
      // proof field exists.
      this.steps=beforeClass;
      return retainedEqual.call(this,a,b,ctx);
    }
    stats.classified++;
    stats.proofFields+=mask.filter(Boolean).length;

    // Only speculate when at least one proof field actually differs. Otherwise
    // ordinary retained equality has nothing expensive to erase here.
    let useful=false;
    for(let i=0;i<mask.length;i++){
      if(mask[i] && sa.args[i]!==sb.args[i] && !this.same(sa.args[i],sb.args[i])){
        useful=true;break;
      }
    }
    if(!useful){
      this.steps=beforeClass;
      return retainedEqual.call(this,a,b,ctx);
    }

    const snap={steps:beforeClass,budget:this.budget,frontier:this.conversionFrontier};
    this.budget=Math.min(this.budget,snap.steps+CAP);
    this._ctorProofEraseDepth=1;
    try{
      for(let i=0;i<sa.args.length;i++){
        if(mask[i]){
          stats.proofSkips++;
          continue;
        }
        if(sa.args[i]===sb.args[i] || this.same(sa.args[i],sb.args[i])) continue;
        stats.dataChecks++;
        retainedEqual.call(this,sa.args[i],sb.args[i],ctx);
      }
      stats.success++;
      this._ctorProofEraseDepth=0;
      this.budget=snap.budget;
      return;
    }catch(e){
      this._ctorProofEraseDepth=0;
      this.steps=snap.steps;
      this.budget=snap.budget;
      this.conversionFrontier=snap.frontier;
      stats.fallback++;
      if(!(e instanceof Stop||e instanceof RangeError)) throw e;
      return retainedEqual.call(this,a,b,ctx);
    }
  };
}

function evalRows(mode,enabled,subset){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const before={...stats},t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null});
  }
  const delta={};for(const k of Object.keys(before)) delta[k]=stats[k]-before[k];
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:delta,results};
}

const focusRows=rows.filter(r=>r.name.endsWith("good/perf/fueled-chain.ndjson"));
const focus=evalRows("focus",true,focusRows);
console.log("CTOR_TELESCOPE_PROOF_ERASURE_FOCUS "+JSON.stringify(focus));
if(focus.wrong) throw new Error("focus wrong");
if(focus.results[0]?.status!=="ACCEPT"){
  install(false);
  console.log("CTOR_TELESCOPE_PROOF_ERASURE_STOP "+JSON.stringify({reason:"fueled-not-closed",focus}));
  process.exit(0);
}

const candidate=evalRows("candidate",true,rows);
const baseline=evalRows("baseline",false,rows);
install(false);
if(candidate.wrong||baseline.wrong) throw new Error("wrong verdict");

let protectedChanged=0;
const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"&&c.status!=="UNKNOWN"&&c.status===c.expected)
    resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
  else if(b.status==="UNKNOWN")
    remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
}
const summary={arena_sha256:sha,budget:1_000_000,speculation_cap:CAP,focus,
  baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
    elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved.some(r=>r.name.endsWith("fueled-chain.ndjson")),
  claim_boundary:"Positive constructor congruence modulo proof irrelevance, including LocalDef execution. Proof-valued argument positions are derived from the constructor's own dependent Pi telescope under symbolic binders; proof terms at those positions are never inspected. Every non-proof argument must be syntactically or definitionally equal. Failed probes rollback to retained conversion."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/ctor-telescope-proof-erasure.json",import.meta.url),JSON.stringify(summary,null,2)+"\n");
console.log("CTOR_TELESCOPE_PROOF_ERASURE "+JSON.stringify(summary));
