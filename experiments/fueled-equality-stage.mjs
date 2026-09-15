import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const BUDGET=Number(process.env.BUDGET??3000000);
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

function rawAppHead(e){
  let h=e,n=0;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  return {h,n};
}
function isTarget(a,b,ctx){
  if(!Array.isArray(a)||a[0]!=="pi"||ctx.length!==7)return false;
  const {h,n}=rawAppHead(b);
  return n>0&&Array.isArray(h)&&h[0]==="var"&&h[1]===2;
}
function smallShape(e){
  if(!Array.isArray(e))return typeof e;
  const {h,n}=rawAppHead(e);
  if(n)return "app:"+(h?.[0]??typeof h)+(h?.[0]==="var"?":"+h[1]:"")+":"+n;
  return e[0];
}

const proto=K.Kernel.prototype,retainedEqual=proto.equal;
let hit=false,stageLog=[];
function record(k,name,fn){
  const before=k.steps;
  try{
    const value=fn();
    const item={name,status:"ok",delta:k.steps-before,steps:k.steps,shape:smallShape(value)};
    stageLog.push(item);
    console.log("FUELED_EQUALITY_STAGE "+JSON.stringify(item));
    return value;
  }catch(e){
    const item={name,status:"throw",delta:k.steps-before,steps:k.steps,
      error:String(e?.message??e),stop_status:e?.status??null};
    stageLog.push(item);
    console.log("FUELED_EQUALITY_STAGE "+JSON.stringify(item));
    throw e;
  }
}

proto.equal=function(a,b,ctx=[]){
  if(hit||!isTarget(a,b,ctx))return retainedEqual.call(this,a,b,ctx);
  hit=true;
  console.log("FUELED_EQUALITY_TARGET "+JSON.stringify({
    at_steps:this.steps,ctx:ctx.length,left:smallShape(a),right:smallShape(b),budget:this.budget
  }));
  const rawSame=record(this,"same-raw",()=>this.same(a,b));
  if(rawSame)return;
  const x=record(this,"normal-left",()=>this.normal(a));
  const y=record(this,"normal-right",()=>this.normal(b));
  const normSame=record(this,"same-normal",()=>this.same(x,y));
  if(normSame)return;
  if(this.caps.has("proof-irrelevance")){
    const tx=record(this,"proofType-left",()=>this.proofType(x,ctx));
    const ty=record(this,"proofType-right",()=>this.proofType(y,ctx));
    console.log("FUELED_EQUALITY_PROOF_TYPES "+JSON.stringify({
      left:tx===null?null:smallShape(tx),right:ty===null?null:smallShape(ty)
    }));
  }
  if(this.caps.has("function-eta")){
    record(this,"eta-left",()=>this.functionEtaContract(x));
    record(this,"eta-right",()=>this.functionEtaContract(y));
  }
  if(this.caps.has("unit-eta")){
    record(this,"unit-infer-left",()=>this.normal(this.infer(x,ctx)));
    record(this,"unit-infer-right",()=>this.normal(this.infer(y,ctx)));
  }
  if(this.caps.has("structure-eta")){
    record(this,"structure-eta-lr",()=>this.structureEtaMatches(x,y,ctx));
    record(this,"structure-eta-rl",()=>this.structureEtaMatches(y,x,ctx));
  }
  this.unknown("fueled-equality-stage-diagnostic");
};

const r=K.checkExport(row.input,caps,BUDGET);
proto.equal=retainedEqual;
console.log("FUELED_EQUALITY_STAGE_SUMMARY "+JSON.stringify({
  arena_sha256:sha,budget:BUDGET,hit,stageLog,
  result:{status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    frontier_declaration:r.frontier_declaration??null}
}));
