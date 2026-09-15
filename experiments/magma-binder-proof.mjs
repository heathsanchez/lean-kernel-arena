import {readFileSync} from "node:fs";
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
data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and p=="good/perf/magma-list-pair-n7.ndjson":
      print(json.dumps({"name":p,"input":a.extractfile(m).read().decode("utf-8")}))
      break
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype;
const retainedEqual=proto.equal;
let capture=null;
function bytes(x){ try{return JSON.stringify(x).length}catch{return 0} }
proto.equal=function(a,b,ctx=[]){
  if(Array.isArray(a)&&Array.isArray(b)&&a[0]==="proj"&&b[0]==="proj"&&a[1]===b[1]&&a[2]===b[2]){
    const size=bytes(a)+bytes(b);
    if(!capture||size>capture.size) capture={kernel:this,a,b,ctx:[...ctx],size,steps:this.steps};
  }
  return retainedEqual.call(this,a,b,ctx);
};
let result;
try{ result=K.checkExport(row.input,caps,1_000_000); }
finally{ proto.equal=retainedEqual; }
if(!capture) throw new Error("same projection not captured");

const kernel=capture.kernel;
kernel.budget=Math.max(kernel.budget,kernel.steps+5_000_000);
const left=kernel.normal(capture.a),right=kernel.normal(capture.b);

function firstDiff(a,b){
  const stack=[{a,b,path:[]}];
  while(stack.length){
    const f=stack.pop();
    if(f.a===f.b) continue;
    const aa=Array.isArray(f.a),bb=Array.isArray(f.b);
    if(!aa||!bb){
      if(f.a!==f.b) return {...f,left:f.a,right:f.b};
      continue;
    }
    if(f.a.length!==f.b.length||f.a[0]!==f.b[0]) return {...f,left:f.a,right:f.b};
    for(let i=0;i<f.a.length;i++){
      const x=f.a[i],y=f.b[i];
      if(!Array.isArray(x)&&!Array.isArray(y)&&x!==y)
        return {path:[...f.path,i],left:x,right:y,parentLeft:f.a,parentRight:f.b};
      if(Array.isArray(x)!==Array.isArray(y))
        return {path:[...f.path,i],left:x,right:y,parentLeft:f.a,parentRight:f.b};
    }
    for(let i=f.a.length-1;i>=0;i--)
      if(Array.isArray(f.a[i])||Array.isArray(f.b[i]))
        stack.push({a:f.a[i],b:f.b[i],path:[...f.path,i]});
  }
  return null;
}
const diff=firstDiff(left,right);
if(!diff) throw new Error("no difference");
function atPathWithCtx(root,path,baseCtx){
  let cur=root,ctx=[...baseCtx];
  for(const idx of path){
    if(Array.isArray(cur)){
      if((cur[0]==="lam"||cur[0]==="pi")&&idx===2) ctx=[...ctx,cur[1]];
      else if(cur[0]==="let"&&idx===3) ctx=[...ctx,cur[1]];
      cur=cur[idx];
    }
  }
  return {term:cur,ctx};
}
const loc=atPathWithCtx(left,diff.path,capture.ctx);
const lv=Array.isArray(diff.parentLeft)&&diff.parentLeft[0]==="var"?diff.parentLeft:null;
const rv=Array.isArray(diff.parentRight)&&diff.parentRight[0]==="var"?diff.parentRight:null;
if(!lv||!rv) throw new Error("first mismatch is not var pair");
const ctx=atPathWithCtx(left,diff.path.slice(0,-1),capture.ctx).ctx;

function brief(x){
  const s=JSON.stringify(x);
  return {bytes:s.length,text:s.slice(0,1200)};
}
function probeProof(v){
  const before=kernel.steps;
  kernel.budget=Math.max(kernel.budget,kernel.steps+2_000_000);
  try{
    const t=kernel.proofType(v,ctx);
    return {isProof:t!==null,steps:kernel.steps-before,type:t===null?null:brief(t),term:v};
  }catch(e){
    if(e instanceof Stop||e instanceof RangeError)
      return {isProof:null,steps:kernel.steps-before,error:e.reason??e.name,term:v};
    throw e;
  }
}
const lp=probeProof(lv),rp=probeProof(rv);
let typeEquality=null;
if(lp.isProof&&rp.isProof){
  const lt=kernel.proofType(lv,ctx),rt=kernel.proofType(rv,ctx);
  const before=kernel.steps;
  kernel.budget=Math.max(kernel.budget,kernel.steps+2_000_000);
  try{
    kernel.equal(lt,rt,ctx);
    typeEquality={equal:true,steps:kernel.steps-before};
  }catch(e){
    if(e instanceof Stop||e instanceof RangeError)
      typeEquality={equal:false,steps:kernel.steps-before,reason:e.reason??e.name};
    else throw e;
  }
}
const entryL=ctx[ctx.length-1-lv[1]],entryR=ctx[ctx.length-1-rv[1]];
console.log("MAGMA_BINDER_PROOF "+JSON.stringify({
  arena_sha256:sha,
  result:{status:result.status,reason:result.reason,steps:result.steps},
  capture:{steps:capture.steps,ctx_depth:capture.ctx.length,size:capture.size},
  normalized:{left_bytes:bytes(left),right_bytes:bytes(right)},
  diff:{path:diff.path,leftVar:lv[1],rightVar:rv[1],ctx_depth:ctx.length,
    outerLeft:lv[1]-(ctx.length-capture.ctx.length),outerRight:rv[1]-(ctx.length-capture.ctx.length)},
  entries:{leftSameRight:entryL===entryR,left:brief(entryL),right:brief(entryR)},
  proof:{left:lp,right:rp,typeEquality}
}));
