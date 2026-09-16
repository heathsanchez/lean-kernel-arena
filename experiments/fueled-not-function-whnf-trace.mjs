import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as P from "../genesis/production.mjs";
import {Kernel,Stop} from "../genesis/kernel-base.mjs";

const BUDGET=Number(process.env.BUDGET??2_000_000);
const expectedHash="f915a7c0e688bbdcbb117e4fbb8cbe26c1ad4388da7712dea641bc6041b3e8bc";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed: "+sha);
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

function shape(e){
  if(!Array.isArray(e))return typeof e;
  let h=e,n=0;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  if(n){
    if(h?.[0]==="const")return `app:const:${h[1]}:${n}`;
    if(h?.[0]==="var")return `app:var:${h[1]}:${n}`;
    return `app:${h?.[0]??typeof h}:${n}`;
  }
  if(e[0]==="const")return `const:${e[1]}`;
  if(e[0]==="var")return `var:${e[1]}`;
  return e[0];
}
function short(e,n=900){
  try{return JSON.stringify(e).slice(0,n);}catch{return String(e).slice(0,n);}
}
function funext(k){return typeof k.currentDeclaration==="string" && k.currentDeclaration.includes('"funext"');}

const proto=Kernel.prototype,whnf0=proto.whnf,infer0=proto.infer;
const recent=[];
let whnfSeq=0,failures=0;
proto.whnf=function(term){
  const before=this.steps,flags={
    full:this._fullStackSafe===true,
    reentry:this.__whnfReentryStackSafe===true,
    depth:this.__retainedWhnfDepth??0,
    localDefs:this.localDefs===true,
    ctx:(this._activeCtx??[]).length
  };
  try{
    const out=whnf0.call(this,term);
    if(funext(this)){
      recent.push({seq:++whnfSeq,before,after:this.steps,delta:this.steps-before,flags,
        input:shape(term),output:shape(out),same:term===out,
        input_term:short(term),output_term:short(out)});
      if(recent.length>120)recent.shift();
    }
    return out;
  }catch(e){
    if(funext(this)){
      recent.push({seq:++whnfSeq,before,after:this.steps,delta:this.steps-before,flags,
        input:shape(term),throw:String(e?.message??e),status:e?.status??null,input_term:short(term)});
      if(recent.length>120)recent.shift();
    }
    throw e;
  }
};
proto.infer=function(term,ctx=[]){
  try{return infer0.call(this,term,ctx);}
  catch(e){
    if(e instanceof Stop && e.status==="REJECT" && e.message==="not-a-function" && funext(this)){
      failures++;
      console.log("FUELED_NOT_FUNCTION "+JSON.stringify({
        failure:failures,steps:this.steps,ctx:ctx.length,term:shape(term),term_json:short(term,1600),
        flags:{full:this._fullStackSafe===true,reentry:this.__whnfReentryStackSafe===true,
          depth:this.__retainedWhnfDepth??0,localDefs:this.localDefs===true,activeCtx:(this._activeCtx??[]).length},
        recent:[...recent]
      }));
    }
    throw e;
  }
};

const r=P.checkExport(row.input,{semanticBudget:BUDGET,inputBytes:20_000_000,recordLimit:400_000});
proto.whnf=whnf0;proto.infer=infer0;
console.log("FUELED_NOT_FUNCTION_SUMMARY "+JSON.stringify({arena_sha256:sha,budget:BUDGET,failures,
  result:{status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    frontier_declaration:r.frontier_declaration??null,fallback_attempt_reason:r.fallback_attempt_reason??null,
    fallback_attempt_steps:r.fallback_attempt_steps??null}}));
