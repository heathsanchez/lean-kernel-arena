import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
wanted={"args-before-unfold.ndjson","folded-constant-first.ndjson","folded-constant-last.ndjson",
"refute-cheap-first.ndjson","refute-cheap-last.ndjson","unroll-versus-evaluate.ndjson"}
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if not m.isfile() or m.name.rsplit("/",1)[-1] not in wanted: continue
    p=m.name.split("/"); e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
const proto=K.Kernel.prototype, retained=proto.equal, CAP=250000;
function rawSpine(e){const args=[];while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}args.reverse();return {head:e,args};}
function cheapPair(a,b){
  if(a===b)return -1000000;
  if(!Array.isArray(a)||!Array.isArray(b))return 0;
  if(a[0]!==b[0])return -10000;
  if(["const","var","nat","strlit","sort"].includes(a[0]))return -5000;
  let score=0,stack=[a,b],seen=new Set();
  while(stack.length&&score<128){const x=stack.pop();if(!Array.isArray(x)||seen.has(x))continue;seen.add(x);score++;for(let i=1;i<x.length;i++)if(Array.isArray(x[i]))stack.push(x[i]);}
  return score;
}
function install(candidate){
  proto.equal=retained;
  if(!candidate)return;
  proto.equal=function(a,b,ctx=[]){
    if(this.localDefs)return retained.call(this,a,b,ctx);
    if(this.same(a,b))return;
    const sa=rawSpine(a),sb=rawSpine(b);
    const sameHead=sa.args.length>0&&sa.args.length===sb.args.length&&(sa.head===sb.head||this.same(sa.head,sb.head));
    const d=sameHead&&sa.head?.[0]==="const"?this.env.get(sa.head[1]):null;
    if(!(sameHead&&d?.kind==="def"))return retained.call(this,a,b,ctx);

    const outer=(this._defSpineDepth??0)===0;
    let snap=null;
    if(outer){
      snap={steps:this.steps,frontier:this.conversionFrontier,budget:this.budget};
      this.budget=Math.min(this.budget,this.steps+CAP);
    }
    this._defSpineDepth=(this._defSpineDepth??0)+1;
    const order=sa.args.map((_,i)=>i).sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
    try{
      for(const i of order)this.equal(sa.args[i],sb.args[i],ctx);
      this._defSpineDepth--;
      if(outer)this.budget=snap.budget;
      return;
    }catch(e){
      this._defSpineDepth--;
      if(!(e instanceof Stop||e instanceof RangeError)){
        if(outer)this.budget=snap.budget;
        throw e;
      }
      if(outer){
        this.budget=snap.budget;this.steps=snap.steps;this.conversionFrontier=snap.frontier;
        return retained.call(this,a,b,ctx);
      }
      // A nested speculative failure declines only that sub-congruence and tries
      // the retained converter while still inside the outer 250k transaction.
      return retained.call(this,a,b,ctx);
    }
  };
}
for(const candidate of [false,true]){
  install(candidate);
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    console.log("RECURSIVE_DEF_SPINE "+JSON.stringify({mode:candidate?"candidate":"baseline",name:row.name,
      expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,
      correct:r.status==="UNKNOWN"||r.status===row.expected}));
  }
}
proto.equal=retained;
