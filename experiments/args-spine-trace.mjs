import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.endswith("good/perf/args-before-unfold.ndjson"):
      print(json.dumps({"name":m.name,"input":a.extractfile(m).read().decode("utf-8")}));break
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:10000000,timeout:10000}));
const proto=K.Kernel.prototype, retained=proto.equal, oldResult=proto.result, CAP=250000;
function rawSpine(e){const args=[];while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}args.reverse();return {head:e,args};}
function cheapPair(a,b){
  if(a===b)return -1000000;if(!Array.isArray(a)||!Array.isArray(b))return 0;
  if(a[0]!==b[0])return -10000;if(["const","var","nat","strlit","sort"].includes(a[0]))return -5000;
  let score=0,stack=[a,b],seen=new Set();
  while(stack.length&&score<128){const x=stack.pop();if(!Array.isArray(x)||seen.has(x))continue;seen.add(x);score++;for(let i=1;i<x.length;i++)if(Array.isArray(x[i]))stack.push(x[i]);}
  return score;
}
proto.equal=function(a,b,ctx=[]){
  if(this.same(a,b))return;
  const sa=rawSpine(a),sb=rawSpine(b);
  if(sa.args.length>0&&sa.args.length===sb.args.length&&(sa.head===sb.head||this.same(sa.head,sb.head))){
    this.__spineTrace??={success:[],fail:[],calls:0,maxDepth:0};
    const tr=this.__spineTrace,depth=this.__spineDepth??0;tr.calls++;tr.maxDepth=Math.max(tr.maxDepth,depth);
    const d=sa.head?.[0]==="const"?this.env.get(sa.head[1]):null;
    const meta={depth,headTag:sa.head?.[0]??typeof sa.head,declKind:d?.kind??null,arity:sa.args.length,
      declaration:this.currentDeclaration??null,name:sa.head?.[0]==="const"?sa.head[1]:null};
    const s={steps:this.steps,frontier:this.conversionFrontier,budget:this.budget};
    this.budget=Math.min(this.budget,this.steps+CAP);this.__spineDepth=depth+1;
    try{
      const order=sa.args.map((_,i)=>i).sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
      for(const i of order)this.equal(sa.args[i],sb.args[i],ctx);
      this.__spineDepth=depth;this.budget=s.budget;
      if(tr.success.length<200)tr.success.push({...meta,used:this.steps-s.steps});
      return;
    }catch(e){
      this.__spineDepth=depth;this.budget=s.budget;
      if(!(e instanceof Stop||e instanceof RangeError))throw e;
      if(tr.fail.length<100)tr.fail.push({...meta,used:this.steps-s.steps,reason:e instanceof Stop?e.message:"RangeError"});
      this.steps=s.steps;this.conversionFrontier=s.frontier;
    }
  }
  return retained.call(this,a,b,ctx);
};
proto.result=function(...args){const r=oldResult.apply(this,args);r.spine_trace=this.__spineTrace??null;return r;};
const r=K.checkExport(row.input,caps,1_000_000);
proto.equal=retained;proto.result=oldResult;
const tr=r.spine_trace??{success:[],fail:[],calls:0,maxDepth:0};
const agg={};
for(const x of tr.success){const k=[x.depth,x.headTag,x.declKind,x.arity].join("|");const a=agg[k]??={depth:x.depth,headTag:x.headTag,declKind:x.declKind,arity:x.arity,count:0,used:0,maxUsed:0};a.count++;a.used+=x.used;a.maxUsed=Math.max(a.maxUsed,x.used);agg[k]=a;}
console.log("ARGS_SPINE_TRACE "+JSON.stringify({status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
  calls:tr.calls,maxDepth:tr.maxDepth,successCount:tr.success.length,failCount:tr.fail.length,
  aggregate:Object.values(agg).sort((a,b)=>b.used-a.used),topSuccess:tr.success.sort((a,b)=>b.used-a.used).slice(0,30),
  topFail:tr.fail.sort((a,b)=>b.used-a.used).slice(0,20)}));
