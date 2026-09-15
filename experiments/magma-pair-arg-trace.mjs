import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop,UNKNOWN} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
wanted={"good/perf/magma-list-pair-n7.ndjson","good/perf/magma-list-pair-n21.ndjson"}
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and p in wanted:
      rows.append({"name":p,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype,retained=proto.equal;
function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {head:h,args};
}
function tag(e){
  if(!Array.isArray(e)) return typeof e;
  if(e[0]==="const") return "const:"+e[1];
  if(e[0]==="app"){
    const s=rawSpine(e),h=s.head;
    return "app:"+(Array.isArray(h)&&h[0]==="const"?h[1]:h?.[0])+":"+s.args.length;
  }
  if(e[0]==="proj") return "proj:"+e[1]+":"+e[2];
  return e[0];
}
const diagnostics=[];
proto.equal=function(a,b,ctx=[]){
  if((this._pairArgTraceDepth??0)>0) return retained.call(this,a,b,ctx);
  try{return retained.call(this,a,b,ctx);}
  catch(e){
    if(!(e instanceof Stop)||e.status!==UNKNOWN||e.message!=="conversion-frontier") throw e;
    let x,y;
    try{x=this.normal(a);y=this.normal(b);}catch(_){throw e;}
    if(!Array.isArray(x)||!Array.isArray(y)||x[0]!=="proj"||y[0]!=="proj"||
       x[1]!==y[1]||x[2]!==y[2]) throw e;
    const sx=rawSpine(x[3]),sy=rawSpine(y[3]);
    const sameHead=sx.args.length===sy.args.length&&sx.args.length>0&&
      (sx.head===sy.head||this.same(sx.head,sy.head));
    if(!sameHead) throw e;

    const record={decl:this.currentDeclaration??null,ctx_depth:ctx.length,
      projection:[x[1],x[2]],head:tag(sx.head),arity:sx.args.length,args:[]};
    this._pairArgTraceDepth=1;
    for(let i=0;i<sx.args.length;i++){
      const before=this.steps,oldBudget=this.budget,oldFrontier=this.conversionFrontier;
      this.budget=Math.min(oldBudget,this.steps+250000);
      let outcome="EQUAL",reason=null;
      try{retained.call(this,sx.args[i],sy.args[i],ctx);}
      catch(err){
        outcome=err instanceof Stop?err.status:err?.constructor?.name??"ERROR";
        reason=err?.message??String(err);
      }
      record.args.push({i,left:tag(sx.args[i]),right:tag(sy.args[i]),
        same:this.same(sx.args[i],sy.args[i]),outcome,reason,spent:this.steps-before,
        frontier:this.conversionFrontier?{
          ctx_depth:this.conversionFrontier.ctx_depth,
          left_bytes:this.conversionFrontier.left_bytes,
          right_bytes:this.conversionFrontier.right_bytes,
          left:(this.conversionFrontier.left??"").slice(0,300),
          right:(this.conversionFrontier.right??"").slice(0,300)
        }:null});
      this.steps=before;this.budget=oldBudget;this.conversionFrontier=oldFrontier;
    }
    this._pairArgTraceDepth=0;
    diagnostics.push(record);
    throw e;
  }
};

for(const row of rows){
  const r=K.checkExport(row.input,caps,1_000_000);
  console.log("MAGMA_PAIR_ARG_TRACE_RESULT "+JSON.stringify({name:row.name,status:r.status,reason:r.reason,steps:r.steps}));
}
proto.equal=retained;
for(const d of diagnostics.slice(-8)) console.log("MAGMA_PAIR_ARG_TRACE "+JSON.stringify(d));
