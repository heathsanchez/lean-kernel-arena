import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

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
const focusRows=rows.filter(r=>r.name.endsWith("good/perf/fueled-chain.ndjson"));

const proto=K.Kernel.prototype,retainedEqual=proto.equal;
const stats={piProbe:0,piSuccess:0,rigidProbe:0,rigidSuccess:0,rigidFallback:0,argChecks:0};

function appHeadVar(e){
  if(!Array.isArray(e)||e[0]!=="app")return false;
  let h=e;while(Array.isArray(h)&&h[0]==="app")h=h[1];
  return Array.isArray(h)&&h[0]==="var";
}
function rawPiEligible(a,b){
  return (Array.isArray(a)&&a[0]==="pi"&&appHeadVar(b))||
         (Array.isArray(b)&&b[0]==="pi"&&appHeadVar(a));
}
function spine(e){
  const args=[];while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse();return {head:e,args};
}
function cheapPair(a,b){
  if(a===b)return -1000000;
  if(!Array.isArray(a)||!Array.isArray(b))return 0;
  if(a[0]!==b[0])return -10000;
  if(["const","var","nat","strlit","sort"].includes(a[0]))return -5000;
  return 0;
}

function install(enabled){
  proto.equal=retainedEqual;
  if(!enabled)return;
  proto.equal=function(a,b,ctx=[]){
    if(this.localDefs!==true)return retainedEqual.call(this,a,b,ctx);

    if(rawPiEligible(a,b)){
      stats.piProbe++;
      const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
      this.budget=Math.min(this.budget,this.steps+100000);
      try{
        const x=this.whnf(a),y=this.whnf(b);
        if(x?.[0]==="pi"&&y?.[0]==="pi"){
          this.budget=snap.budget;
          this.equal(x[1],y[1],ctx);
          this.equal(x[2],y[2],[...ctx,x[1]]);
          stats.piSuccess++;
          return;
        }
      }catch(e){
        if(!(e instanceof Stop||e instanceof RangeError))throw e;
      }
      this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    }

    if(a===b)return;
    const sa=spine(a),sb=spine(b);
    const sameHead=sa.args.length>0&&sa.args.length===sb.args.length&&
      (sa.head===sb.head||(Array.isArray(sa.head)&&Array.isArray(sb.head)&&this.same(sa.head,sb.head)));
    const d=sameHead&&sa.head?.[0]==="const"?this.env.get(sa.head[1]):null;
    if(!sameHead||d?.kind!=="inductive")
      return retainedEqual.call(this,a,b,ctx);

    stats.rigidProbe++;
    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    this.budget=Math.min(this.budget,this.steps+250000);
    const order=sa.args.map((_,i)=>i).sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
    try{
      for(const i of order){
        if(sa.args[i]===sb.args[i])continue;
        stats.argChecks++;
        this.equal(sa.args[i],sb.args[i],ctx);
      }
      this.budget=snap.budget;
      stats.rigidSuccess++;
      return;
    }catch(e){
      if(!(e instanceof Stop||e instanceof RangeError)){this.budget=snap.budget;throw e;}
      stats.rigidFallback++;
      this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
      return retainedEqual.call(this,a,b,ctx);
    }
  };
}

function evalRows(mode,enabled,subset){
  install(enabled);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
      fallback_mode:r.fallback_mode??null,fallback_attempt_reason:r.fallback_attempt_reason??null});
  }
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results};
}

const focus=evalRows("focus-candidate",true,focusRows);
console.log("LOCALDEF_RIGID_CONGRUENCE_FOCUS "+JSON.stringify(focus));
if(focus.wrong)throw new Error("focus wrong");
if(focus.results[0]?.status!=="ACCEPT"){install(false);process.exit(0);}

const candidate=evalRows("candidate",true,rows);
const baseline=evalRows("baseline",false,rows);
install(false);
if(candidate.wrong||baseline.wrong)throw new Error("wrong verdict");
let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"){
    if(c.status!=="UNKNOWN"&&c.status===c.expected)resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
    else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,frontier_declaration:c.frontier_declaration});
  }
}
console.log("LOCALDEF_RIGID_CONGRUENCE "+JSON.stringify({
  arena_sha256:sha,budget:1000000,
  baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
    elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved.some(r=>r.name.endsWith("fueled-chain.ndjson")),
  claim_boundary:"LocalDef execution ordering only. Raw Pi versus variable-headed application may WHNF both sides and use the already-retained Pi congruence rule when both become Pi. Exact same-head applications of an installed inductive type may prove equality by recursively proving every argument equal under the exact local context. Both probes are bounded and restore semantic steps/frontier on failure; no new definitional equality rule is added."
}));
