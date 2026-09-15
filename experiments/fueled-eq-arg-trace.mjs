import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop,UNKNOWN} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.endswith("good/perf/fueled-chain.ndjson"):
      print(json.dumps({"input":a.extractfile(m).read().decode("utf-8")}))
      break
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype,retained=proto.equal;
const diagnostics=[];
function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {head:h,args};
}
function tag(e){
  if(!Array.isArray(e))return typeof e;
  const s=spine(e);
  if(s.args.length){
    if(s.head?.[0]==="const")return "app:const:"+s.head[1]+":"+s.args.length;
    if(s.head?.[0]==="var")return "app:var:"+s.head[1]+":"+s.args.length;
    return "app:"+(s.head?.[0]??typeof s.head)+":"+s.args.length;
  }
  if(e[0]==="const")return "const:"+e[1];
  return e[0];
}
function isEqHead(k,h){
  if(!Array.isArray(h)||h[0]!=="const")return false;
  const d=k.env.get(h[1]);
  return d?.kind==="inductive" && /"Eq"]$/.test(h[1]);
}
proto.equal=function(a,b,ctx=[]){
  if((this._fueledEqArgTraceDepth??0)>0)return retained.call(this,a,b,ctx);
  const sa=spine(a),sb=spine(b);
  const target=ctx.length===7&&sa.args.length===3&&sb.args.length===3&&
    isEqHead(this,sa.head)&&isEqHead(this,sb.head)&&
    (sa.head===sb.head||this.same(sa.head,sb.head));
  const before=this.steps;
  try{return retained.call(this,a,b,ctx);}
  catch(original){
    if(!target||!(original instanceof Stop)||original.status!==UNKNOWN)throw original;
    const record={currentDeclaration:this.currentDeclaration??null,before,after:this.steps,spent:this.steps-before,
      left:tag(a),right:tag(b),ctx:ctx.length,args:[]};
    this._fueledEqArgTraceDepth=1;
    const saved={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    for(let i=0;i<3;i++){
      const start=this.steps;
      const oldFrontier=this.conversionFrontier;
      this.budget=this.steps+500000;
      let outcome="EQUAL",reason=null;
      try{retained.call(this,sa.args[i],sb.args[i],ctx);}
      catch(e){outcome=e instanceof Stop?e.status:(e?.constructor?.name??"ERROR");reason=e?.message??String(e);}
      record.args.push({i,left:tag(sa.args[i]),right:tag(sb.args[i]),
        same:sa.args[i]===sb.args[i]||this.same(sa.args[i],sb.args[i]),
        outcome,reason,spent:this.steps-start,
        frontier:this.conversionFrontier?{
          ctx_depth:this.conversionFrontier.ctx_depth,
          left_bytes:this.conversionFrontier.left_bytes,
          right_bytes:this.conversionFrontier.right_bytes,
          left:(this.conversionFrontier.left??"").slice(0,400),
          right:(this.conversionFrontier.right??"").slice(0,400)
        }:null});
      this.steps=start;
      this.conversionFrontier=oldFrontier;
    }
    this._fueledEqArgTraceDepth=0;
    this.steps=saved.steps;this.budget=saved.budget;this.conversionFrontier=saved.frontier;
    diagnostics.push(record);
    throw original;
  }
};
const r=K.checkExport(row.input,caps,1_000_000);
proto.equal=retained;
console.log("FUELED_EQ_ARG_RESULT "+JSON.stringify({status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed,
  frontier_declaration:r.frontier_declaration??null,fallback_attempt_reason:r.fallback_attempt_reason??null}));
for(const d of diagnostics)console.log("FUELED_EQ_ARG_TRACE "+JSON.stringify(d));
