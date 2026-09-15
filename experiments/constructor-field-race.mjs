// Prospective fair constructor-field race.
//
// Soundness boundary:
// - both raw terms must be fully-applied occurrences of the exact same installed
//   inductive constructor;
// - all constructor parameters must be syntactically identical under retained same();
// - each data field gets a small conversion slice using the retained converter;
// - only a retained definitive REJECT from a field is propagated;
// - success/inconclusive slices never manufacture a verdict; if no field rejects,
//   the whole comparison falls back to the retained converter unchanged.
//
// This is fair bounded exploration, not cheapness guessing. Speculative work is
// charged to the semantic step budget; only the temporary budget cap/frontier
// are restored between slices.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop,REJECT} from "../genesis/kernel-base.mjs";

const QUANTUM=Number(process.env.QUANTUM??5000);
if(!Number.isSafeInteger(QUANTUM)||QUANTUM<100||QUANTUM>50000) throw new Error("bad QUANTUM");
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
const retainedEqual=proto.equal;
const stats={eligible:0,slices:0,sliceSuccess:0,sliceUnknown:0,sliceReject:0,rejectNames:new Map()};

function rawSpine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse();
  return {head:e,args};
}
function nameOf(k,head){
  if(!Array.isArray(head)||head[0]!=="const") return null;
  return k.env.get(head[1])??null;
}
function install(enabled){
  proto.equal=retainedEqual;
  if(!enabled) return;
  proto.equal=function(a,b,ctx=[]){
    if(this._ctorRaceDepth) return retainedEqual.call(this,a,b,ctx);
    if(a===b) return;
    const sa=rawSpine(a),sb=rawSpine(b);
    if(sa.args.length===0||sa.args.length!==sb.args.length) return retainedEqual.call(this,a,b,ctx);
    if(!(sa.head===sb.head||this.same(sa.head,sb.head))) return retainedEqual.call(this,a,b,ctx);
    const d=nameOf(this,sa.head);
    if(d?.kind!=="ctor") return retainedEqual.call(this,a,b,ctx);
    const nP=d.numParams??0,nF=d.numFields??0;
    if(sa.args.length!==nP+nF||nF<1) return retainedEqual.call(this,a,b,ctx);
    for(let i=0;i<nP;i++) if(!this.same(sa.args[i],sb.args[i]))
      return retainedEqual.call(this,a,b,ctx);

    stats.eligible++;
    const originalBudget=this.budget;
    this._ctorRaceDepth=1;
    try{
      for(let i=nP;i<nP+nF;i++){
        stats.slices++;
        const frontier=this.conversionFrontier;
        const sliceLimit=Math.min(originalBudget,this.steps+QUANTUM);
        this.budget=sliceLimit;
        try{
          retainedEqual.call(this,sa.args[i],sb.args[i],ctx);
          stats.sliceSuccess++;
        }catch(e){
          if(e instanceof Stop && e.status===REJECT){
            stats.sliceReject++;
            const key=this.currentDeclaration??"<none>";
            stats.rejectNames.set(key,(stats.rejectNames.get(key)??0)+1);
            this.budget=originalBudget;
            throw e;
          }
          if(!(e instanceof Stop||e instanceof RangeError)) throw e;
          stats.sliceUnknown++;
          this.conversionFrontier=frontier;
        }finally{
          this.budget=originalBudget;
        }
      }
    }finally{
      this._ctorRaceDepth=0;
      this.budget=originalBudget;
    }
    return retainedEqual.call(this,a,b,ctx);
  };
}
function evaluate(mode,enabled,subset){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const before={eligible:stats.eligible,slices:stats.slices,sliceSuccess:stats.sliceSuccess,
    sliceUnknown:stats.sliceUnknown,sliceReject:stats.sliceReject};
  const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null});
  }
  const delta={};
  for(const k of Object.keys(before)) delta[k]=stats[k]-before[k];
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:delta,results};
}

const focusRows=rows.filter(r=>r.name.includes("refute-cheap-"));
const focus=evaluate("focus-candidate",true,focusRows);
console.log("CTOR_FIELD_RACE_FOCUS "+JSON.stringify({quantum:QUANTUM,focus}));
if(focus.wrong) throw new Error("focus wrong verdict");
if(focus.results.some(r=>r.status!=="REJECT")){
  install(false);
  console.log("CTOR_FIELD_RACE_STOP "+JSON.stringify({reason:"focus-not-closed",focus}));
  process.exit(0);
}

// Candidate first so it does not inherit a warmed baseline process.
const candidate=evaluate("candidate",true,rows);
const baseline=evaluate("baseline",false,rows);
install(false);
if(candidate.wrong||baseline.wrong) throw new Error("wrong verdict");

let protectedChanged=0;
const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++;
    regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"&&c.status!== "UNKNOWN"&&c.status===c.expected)
    resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
  else if(b.status==="UNKNOWN")
    remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
}
const summary={arena_sha256:sha,quantum:QUANTUM,budget:1_000_000,focus,
  baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
    elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved.some(r=>r.name.includes("refute-cheap-")),
  claim_boundary:"Fully-applied exact same verified constructor only; exact constructor parameters must syntactically agree. Each data field receives the same bounded retained-conversion slice. Only a definitive retained REJECT is propagated; all inconclusive exploration is charged and the outer comparison otherwise falls back unchanged."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/constructor-field-race.json",import.meta.url),JSON.stringify(summary,null,2)+"\n");
console.log("CTOR_FIELD_RACE "+JSON.stringify(summary));
