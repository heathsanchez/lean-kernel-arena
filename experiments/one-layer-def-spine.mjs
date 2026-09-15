import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
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

const proto=K.Kernel.prototype,retained=proto.equal,CAP=250000;
function rawSpine(e){const args=[];while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}args.reverse();return {head:e,args};}
function cheapPair(a,b){
 if(a===b)return -1000000;if(!Array.isArray(a)||!Array.isArray(b))return 0;
 if(a[0]!==b[0])return -10000;if(["const","var","nat","strlit","sort"].includes(a[0]))return -5000;
 let score=0,stack=[a,b],seen=new Set();
 while(stack.length&&score<128){const x=stack.pop();if(!Array.isArray(x)||seen.has(x))continue;seen.add(x);score++;for(let i=1;i<x.length;i++)if(Array.isArray(x[i]))stack.push(x[i]);}
 return score;
}
function exposeDef(kernel,e){
 const s=rawSpine(e);
 if(s.head?.[0]!=="const")return null;
 const d=kernel.env.get(s.head[1]);
 if(d?.kind!=="def")return null;
 let f=kernel.instantiateDeclaration(s.head,d.value),i=0;
 while(i<s.args.length&&Array.isArray(f)&&f[0]==="lam"){
   f=kernel.substitute(f[2],s.args[i++]);
 }
 for(;i<s.args.length;i++)f=kernel.make("app",f,s.args[i]);
 return f;
}
function install(enabled){
 proto.equal=retained;
 if(!enabled)return;
 proto.equal=function(a,b,ctx=[]){
  if(this.localDefs)return retained.call(this,a,b,ctx);
  if(this.same(a,b))return;
  const depth=this._oneLayerDepth??0,sa=rawSpine(a),sb=rawSpine(b);
  const sameHead=sa.args.length>0&&sa.args.length===sb.args.length&&(sa.head===sb.head||this.same(sa.head,sb.head));
  const d=sameHead&&sa.head?.[0]==="const"?this.env.get(sa.head[1]):null;
  // A rigid inductive application starts the transaction. Inside it we may
  // decompose exact same heads or expose one transparent def layer on either side.
  if(depth===0&&(!sameHead||d?.kind!=="inductive"))return retained.call(this,a,b,ctx);

  const outer=depth===0;let snap=null;
  if(outer){snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};this.budget=Math.min(this.budget,this.steps+CAP);}
  this._oneLayerDepth=depth+1;
  try{
    if(sameHead){
      const order=sa.args.map((_,i)=>i).sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
      for(const i of order)this.equal(sa.args[i],sb.args[i],ctx);
      this._oneLayerDepth=depth;if(outer)this.budget=snap.budget;return;
    }
    const ax=exposeDef(this,a),bx=exposeDef(this,b);
    if(ax!==null||bx!==null){
      this.equal(ax??a,bx??b,ctx);
      this._oneLayerDepth=depth;if(outer)this.budget=snap.budget;return;
    }
    throw new Stop(K.UNKNOWN,"one-layer-decline");
  }catch(e){
    this._oneLayerDepth=depth;
    if(!(e instanceof Stop||e instanceof RangeError)){if(outer)this.budget=snap.budget;throw e;}
    if(outer){this.budget=snap.budget;this.steps=snap.steps;this.conversionFrontier=snap.frontier;return retained.call(this,a,b,ctx);}
    return retained.call(this,a,b,ctx);
  }
 };
}

const budget=1_000_000;
function evaluate(mode,enabled){
 install(enabled);const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
 for(const row of rows){const r=K.checkExport(row.input,caps,budget);counts[r.status]=(counts[r.status]??0)+1;totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null});}
 return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}
const baseline=evaluate("baseline",false),candidate=evaluate("one-layer-def",true);proto.equal=retained;
if(baseline.wrong||candidate.wrong)throw new Error("wrong verdict");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){const b=baseline.results[i],r=candidate.results[i];if(b.status!=="UNKNOWN"&&r.status!==b.status){protectedChanged++;regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});}if(residual.has(r.name)){if(r.status!=="UNKNOWN"){if(r.status!==r.expected)throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));resolved++;resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});}else remaining.push({name:r.name,reason:r.reason,steps:r.steps});}}
const summary={arena_sha256:sha,budget,speculation_cap:CAP,baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms},protectedChanged,resolved,resolvedCases,regressions,remaining,lawful:candidate.wrong===0&&protectedChanged===0,promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,claim_boundary:"Positive execution consequence only. Inside a rigid-inductive transaction, expose at most one transparent definition layer plus immediate beta binders, then retry exact structural congruence. Failure rolls back to retained conversion."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});writeFileSync(new URL("../genesis/evidence/one-layer-def-spine.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));console.log("ONE_LAYER_DEF_SPINE "+JSON.stringify(summary));
