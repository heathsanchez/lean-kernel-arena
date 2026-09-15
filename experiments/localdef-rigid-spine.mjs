import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

const FOCUS_BUDGET=Number(process.env.FOCUS_BUDGET??1000000);
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
const stats={piProbe:0,piSuccess:0,localVarProbe:0,localVarRelay:0,etaRelay:0,etaExpand:0,outer:0,inner:0,success:0,fallback:0,argChecks:0,maxDepth:0};
const fallbackDetails=[];
function shape(e){
  if(!Array.isArray(e))return typeof e;
  let h=e,n=0;while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  if(n){
    if(Array.isArray(h)&&h[0]==="var")return "app:var:"+h[1]+":"+n;
    if(Array.isArray(h)&&h[0]==="const")return "app:const:"+h[1]+":"+n;
    return "app:"+(h?.[0]??typeof h)+":"+n;
  }
  if(e[0]==="var")return "var:"+e[1];
  if(e[0]==="const")return "const:"+e[1];
  return e[0];
}

function appHeadVar(e){
  if(!Array.isArray(e)||e[0]!=="app")return false;
  let h=e;while(Array.isArray(h)&&h[0]==="app")h=h[1];
  return Array.isArray(h)&&h[0]==="var";
}
function rawPiEligible(a,b){
  return (Array.isArray(a)&&a[0]==="pi"&&appHeadVar(b))||
         (Array.isArray(b)&&b[0]==="pi"&&appHeadVar(a));
}
function varTerm(e){ return Array.isArray(e)&&e[0]==="var"; }
function localVarRelayEligible(a,b){
  // Inside an already-bounded LocalDef congruence transaction, a local
  // variable is not a rigid head: it may carry an exact local definition.
  // Expose that value before any global rigid-head decision.
  return varTerm(a)||varTerm(b);
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
  let score=0,stack=[a,b],seen=new Set();
  while(stack.length&&score<128){
    const x=stack.pop();if(!Array.isArray(x)||seen.has(x))continue;
    seen.add(x);score++;
    for(let i=1;i<x.length;i++)if(Array.isArray(x[i]))stack.push(x[i]);
  }
  return score;
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
    const depth=this._localDefRigidDepth??0;

    if(depth>0 && localVarRelayEligible(a,b) && !this._localVarRelayDepth){
      stats.localVarProbe++;
      const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
      this._localVarRelayDepth=1;
      try{
        const x=this.whnf(a),y=this.whnf(b);
        if(x!==a||y!==b){
          stats.localVarRelay++;
          if(fallbackDetails.length<20) fallbackDetails.push({
            kind:"relay",depth,ctx:ctx.length,beforeLeft:shape(a),beforeRight:shape(b),
            afterLeft:shape(x),afterRight:shape(y),spent:this.steps-snap.steps
          });
          if(this.caps.has("function-eta")){
            const ex=Array.isArray(x)&&x[0]==="lam"?this.functionEtaContract(x):null;
            if(ex!==null){stats.etaRelay++;return this.equal(ex,y,ctx);}
            const ey=Array.isArray(y)&&y[0]==="lam"?this.functionEtaContract(y):null;
            if(ey!==null){stats.etaRelay++;return this.equal(x,ey,ctx);}
            if(Array.isArray(x)&&x[0]==="lam"&&Array.isArray(y)&&y[0]!=="lam"){
              stats.etaExpand++;
              const fy=this.make("app",this.shift(y,1),this.make("var",0));
              return this.equal(x[2],fy,[...ctx,x[1]]);
            }
            if(Array.isArray(y)&&y[0]==="lam"&&Array.isArray(x)&&x[0]!=="lam"){
              stats.etaExpand++;
              const fx=this.make("app",this.shift(x,1),this.make("var",0));
              return this.equal(fx,y[2],[...ctx,y[1]]);
            }
          }
          return this.equal(x,y,ctx);
        }
      }catch(e){
        if(!(e instanceof Stop||e instanceof RangeError))throw e;
      }finally{
        this._localVarRelayDepth=0;
      }
      this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    }
    const sa=spine(a),sb=spine(b);
    const sameHead=sa.args.length>0&&sa.args.length===sb.args.length&&
      (sa.head===sb.head||(Array.isArray(sa.head)&&Array.isArray(sb.head)&&this.same(sa.head,sb.head)));
    const d=sameHead&&sa.head?.[0]==="const"?this.env.get(sa.head[1]):null;
    if(!sameHead||(depth===0&&d?.kind!=="inductive"))
      return retainedEqual.call(this,a,b,ctx);

    const outer=depth===0;
    let snap=null;
    if(outer){
      stats.outer++;
      snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
      this.budget=Math.min(this.budget,this.steps+250000);
    }else stats.inner++;
    this._localDefRigidDepth=depth+1;
    stats.maxDepth=Math.max(stats.maxDepth,depth+1);

    const order=sa.args.map((_,i)=>i)
      .sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
    try{
      for(const i of order){
        if(sa.args[i]===sb.args[i])continue;
        stats.argChecks++;
        try{
          this.equal(sa.args[i],sb.args[i],ctx);
        }catch(e){
          if(fallbackDetails.length<20) fallbackDetails.push({
            kind:"arg-fail",depth:depth+1,ctx:ctx.length,head:sa.head?.[1]??shape(sa.head),index:i,
            left:shape(sa.args[i]),right:shape(sb.args[i]),
            spent:outer?(this.steps-snap.steps):null,error:String(e?.message??e),status:e?.status??null
          });
          throw e;
        }
      }
      this._localDefRigidDepth=depth;
      if(outer)this.budget=snap.budget;
      stats.success++;
      return;
    }catch(e){
      this._localDefRigidDepth=depth;
      if(!(e instanceof Stop||e instanceof RangeError)){
        if(outer)this.budget=snap.budget;
        throw e;
      }
      if(outer){
        stats.fallback++;
        this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
        return retainedEqual.call(this,a,b,ctx);
      }
      return retainedEqual.call(this,a,b,ctx);
    }
  };
}

function evalRows(mode,enabled,subset,budget=1000000){
  install(enabled);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,budget);
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

const focus=evalRows("focus-candidate",true,focusRows,FOCUS_BUDGET);
console.log("LOCALDEF_RIGID_SPINE_FOCUS "+JSON.stringify({...focus,fallbackDetails}));
if(focus.wrong)throw new Error("focus wrong");
if(focus.results[0]?.status!=="ACCEPT"){install(false);process.exit(0);}
if(FOCUS_BUDGET!==1000000){install(false);process.exit(0);}

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
console.log("LOCALDEF_RIGID_SPINE "+JSON.stringify({
  arena_sha256:sha,budget:1000000,
  baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
    elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved.some(r=>r.name.endsWith("fueled-chain.ndjson")),
  claim_boundary:"LocalDef execution ordering only. Raw Pi versus variable-headed application may WHNF both sides and reuse retained Pi congruence when both become Pi. A bounded transaction may start only from exact same-head applications of an installed inductive type; within that transaction only, exact same-head inner application spines may be recursively decomposed. Failure restores semantic steps/frontier before the retained converter. No new equality law is added."
}));
