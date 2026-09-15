// Narrow retained-REJECT escape for rigid inductive type spines.
//
// Existing rigid-type-spine intentionally swallows every Stop and falls back,
// because arbitrary nested same-head applications can be reducible and are not
// injective. This separator recognizes one strictly smaller sound case:
//
//   rigid inductive type application
//      ... (C p1..pn f1..fm) ...
//
// where C is an exact fully-applied constructor of a non-Prop inductive and
// constructor parameters are syntactically identical. Each constructor field
// gets one bounded retained-conversion slice. A definitive retained REJECT from
// any field is conclusive by constructor injectivity and may escape to refute
// the enclosing rigid inductive type application. UNKNOWN/stack exhaustion are
// inconclusive; proof constructors are never used for negative propagation.
//
// Speculative work remains charged.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop,REJECT} from "../genesis/kernel-base.mjs";

const QUANTUM=Number(process.env.QUANTUM??1000);
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
const retainedEqual=proto.equal;
const stats={outerEligible:0,ctorEligible:0,fieldSlices:0,fieldEqual:0,fieldUnknown:0,fieldReject:0,escaped:0};

function spine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse();
  return {head:e,args};
}
function sameHead(k,a,b){
  return a===b||(Array.isArray(a)&&Array.isArray(b)&&k.same(a,b));
}
function probeNonPropCtor(k,a,b,ctx,originalBudget){
  const sa=spine(a),sb=spine(b);
  if(sa.args.length===0||sa.args.length!==sb.args.length||!sameHead(k,sa.head,sb.head))
    return null;
  if(sa.head?.[0]!=="const") return null;
  const ctor=k.env.get(sa.head[1]);
  if(ctor?.kind!=="ctor") return null;
  const ind=k.env.get(ctor.induct);
  if(ind?.kind!=="inductive"||ind.isProp===true) return null;
  const nP=ctor.numParams??0,nF=ctor.numFields??0;
  if(nF<1||sa.args.length!==nP+nF) return null;
  for(let i=0;i<nP;i++) if(!k.same(sa.args[i],sb.args[i])) return null;

  stats.ctorEligible++;
  let allEqual=true;
  for(let i=nP;i<nP+nF;i++){
    if(sa.args[i]===sb.args[i]||k.same(sa.args[i],sb.args[i])) continue;
    stats.fieldSlices++;
    const oldFrontier=k.conversionFrontier;
    k.budget=Math.min(originalBudget,k.steps+QUANTUM);
    k.__rigidCtorEscapeDepth=(k.__rigidCtorEscapeDepth??0)+1;
    try{
      retainedEqual.call(k,sa.args[i],sb.args[i],ctx);
      stats.fieldEqual++;
    }catch(e){
      if(e instanceof Stop&&e.status===REJECT){
        stats.fieldReject++;
        return {reject:e};
      }
      if(!(e instanceof Stop||e instanceof RangeError)) throw e;
      stats.fieldUnknown++;
      allEqual=false;
      k.conversionFrontier=oldFrontier;
    }finally{
      k.__rigidCtorEscapeDepth--;
      k.budget=originalBudget;
    }
  }
  return allEqual?{equal:true}:{unknown:true};
}

function install(enabled){
  proto.equal=retainedEqual;
  if(!enabled) return;
  proto.equal=function(a,b,ctx=[]){
    if(this.__rigidCtorEscapeDepth) return retainedEqual.call(this,a,b,ctx);
    if(a===b) return;
    const sa=spine(a),sb=spine(b);
    const same=sa.args.length>0&&sa.args.length===sb.args.length&&sameHead(this,sa.head,sb.head);
    const outer= same && sa.head?.[0]==="const" ? this.env.get(sa.head[1]) : null;
    if(!same||outer?.kind!=="inductive")
      return retainedEqual.call(this,a,b,ctx);

    stats.outerEligible++;
    const originalBudget=this.budget;
    try{
      for(let i=0;i<sa.args.length;i++){
        if(sa.args[i]===sb.args[i]||this.same(sa.args[i],sb.args[i])) continue;
        const p=probeNonPropCtor(this,sa.args[i],sb.args[i],ctx,originalBudget);
        if(p?.reject){
          stats.escaped++;
          throw p.reject;
        }
      }
    }finally{
      this.budget=originalBudget;
    }
    return retainedEqual.call(this,a,b,ctx);
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
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null});
  }
  const delta={};
  for(const k of Object.keys(before))delta[k]=stats[k]-before[k];
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:delta,results};
}

const focusRows=rows.filter(r=>r.name.includes("refute-cheap-"));
const focus=evalRows("focus",true,focusRows);
console.log("RIGID_CTOR_REJECT_FOCUS "+JSON.stringify({quantum:QUANTUM,focus}));
if(focus.wrong)throw new Error("focus wrong verdict");
if(focus.results.some(r=>r.status!=="REJECT")){
  install(false);
  console.log("RIGID_CTOR_REJECT_STOP "+JSON.stringify({reason:"focus-not-closed",focus}));
  process.exit(0);
}

const candidate=evalRows("candidate",true,rows);
const baseline=evalRows("baseline",false,rows);
install(false);
if(candidate.wrong||baseline.wrong)throw new Error("wrong verdict");

let protectedChanged=0;
const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++;
    regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"&&c.status!=="UNKNOWN"&&c.status===c.expected)
    resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
  else if(b.status==="UNKNOWN")
    remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
}
const summary={arena_sha256:sha,quantum:QUANTUM,budget:1_000_000,focus,
 baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
   elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved.filter(r=>r.name.includes("refute-cheap-")).length===2,
 claim_boundary:"Only while comparing applications of one exact rigid inductive type head. Negative escape is allowed only from a fully-applied constructor of a non-Prop inductive with syntactically identical constructor parameters, after the retained converter itself returns definitive REJECT on a data field. UNKNOWN and stack exhaustion remain inconclusive and fall back."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/rigid-constructor-reject.json",import.meta.url),JSON.stringify(summary,null,2)+"\n");
console.log("RIGID_CTOR_REJECT "+JSON.stringify(summary));
