import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

const BUDGET=Number(process.env.BUDGET??1000000);
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
    if m.isfile() and m.name.endswith("good/perf/fueled-chain.ndjson"):
      rows.append({"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}))[0];
if(!row)throw new Error("missing fueled-chain");

const proto=K.Kernel.prototype,originalEqual=proto.equal;
const lazyStats={probes:0,piPi:0,success:0,fallback:0,spent:0,maxSpent:0};
function appHeadVar(e){
  if(!Array.isArray(e)||e[0]!=="app")return false;
  let h=e;
  while(Array.isArray(h)&&h[0]==="app")h=h[1];
  return Array.isArray(h)&&h[0]==="var";
}
function rawEligible(a,b){
  return (Array.isArray(a)&&a[0]==="pi"&&appHeadVar(b))||
         (Array.isArray(b)&&b[0]==="pi"&&appHeadVar(a));
}
proto.equal=function(a,b,ctx=[]){
  if(this.localDefs!==true||!rawEligible(a,b))
    return originalEqual.call(this,a,b,ctx);
  lazyStats.probes++;
  const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
  this.budget=Math.min(this.budget,this.steps+100000);
  try{
    const x=this.whnf(a),y=this.whnf(b);
    const spent=this.steps-snap.steps;
    lazyStats.spent+=spent;lazyStats.maxSpent=Math.max(lazyStats.maxSpent,spent);
    if(x?.[0]==="pi"&&y?.[0]==="pi"){
      lazyStats.piPi++;this.budget=snap.budget;
      this.equal(x[1],y[1],ctx);
      this.equal(x[2],y[2],[...ctx,x[1]]);
      lazyStats.success++;
      return;
    }
  }catch(e){
    if(!(e instanceof Stop||e instanceof RangeError))throw e;
  }
  lazyStats.fallback++;
  this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
  return originalEqual.call(this,a,b,ctx);
};

const lazyEqual=proto.equal;
function shape(e){
  if(!Array.isArray(e))return typeof e;
  let h=e,n=0;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  if(n){
    if(Array.isArray(h)&&h[0]==="var")return "app:var:"+h[1]+":"+n;
    if(Array.isArray(h)&&h[0]==="const")return "app:const:"+h[1]+":"+n;
    return "app:"+(h?.[0]??typeof h)+":"+n;
  }
  if(e[0]==="var")return "var:"+e[1];
  if(e[0]==="const")return "const:"+e[1];
  return e[0];
}
const shapes=new Map();
let calls=0,success=0,failed=0;
proto.equal=function(a,b,ctx=[]){
  calls++;
  const key=shape(a)+" -> "+shape(b)+" @"+ctx.length;
  let s=shapes.get(key);if(!s){s={calls:0,success:0,failed:0,ticks:0,max:0};shapes.set(key,s);}
  s.calls++;
  const before=this.steps;
  try{
    const out=lazyEqual.call(this,a,b,ctx);
    const d=this.steps-before;s.success++;s.ticks+=d;s.max=Math.max(s.max,d);success++;return out;
  }catch(e){
    const d=this.steps-before;s.failed++;s.ticks+=d;s.max=Math.max(s.max,d);failed++;throw e;
  }
};

const r=K.checkExport(row.input,caps,BUDGET);
proto.equal=originalEqual;
const topShapes=[...shapes.entries()].map(([shape,v])=>({shape,...v}))
  .sort((a,b)=>b.ticks-a.ticks||b.max-a.max||b.calls-a.calls).slice(0,40);
console.log("FUELED_LAZY_PI_PROFILE "+JSON.stringify({
  arena_sha256:sha,budget:BUDGET,
  result:{status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    frontier_declaration:r.frontier_declaration??null,fallback_attempt_reason:r.fallback_attempt_reason??null,
    fallback_attempt_steps:r.fallback_attempt_steps??null},
  lazyStats,calls,success,failed,topShapes
}));
