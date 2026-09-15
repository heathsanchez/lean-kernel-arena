import {readFileSync} from "node:fs";
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
data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.endswith("good/perf/fueled-chain.ndjson"):
      print(json.dumps({"input":a.extractfile(m).read().decode("utf-8")}));break
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype,retained=proto.equal;
function spine(e){const args=[];while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}args.reverse();return{head:e,args};}
function shape(e){
  if(!Array.isArray(e))return typeof e+":"+String(e);
  const s=spine(e);
  if(s.args.length){
    const h=s.head;
    if(Array.isArray(h)&&h[0]==="var")return "app:var:"+h[1]+":"+s.args.length;
    if(Array.isArray(h)&&h[0]==="const")return "app:const:"+h[1]+":"+s.args.length;
    return "app:"+(h?.[0]??typeof h)+":"+s.args.length;
  }
  if(e[0]==="var")return "var:"+e[1];
  if(e[0]==="const")return "const:"+e[1];
  return e[0];
}
function target(a,b,ctx){
  if(ctx.length!==7)return false;
  return (shape(a)==="app:var:0:1"&&shape(b)==="var:4")||
         (shape(b)==="app:var:0:1"&&shape(a)==="var:4");
}
function ctxSummary(ctx){
  return ctx.map((x,i)=>({
    slot:i,
    debruijn:ctx.length-1-i,
    localDef:x?.__localDef===true,
    type:shape(x?.__localDef===true?x.type:x),
    value:x?.__localDef===true?shape(x.value):null
  }));
}
let hit=false;
proto.equal=function(a,b,ctx=[]){
  if(this.localDefs===true&&!hit&&target(a,b,ctx)){
    hit=true;
    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    const rec={at_steps:this.steps,left:shape(a),right:shape(b),ctx:ctxSummary(ctx),probes:[]};
    for(const [name,t] of [["left",a],["right",b]]){
      this.steps=snap.steps;this.budget=Math.min(snap.budget,snap.steps+100000);this.conversionFrontier=snap.frontier;
      const before=this.steps;
      try{
        const w=this.whnf(t);
        rec.probes.push({name,status:"ok",spent:this.steps-before,shape:shape(w),same_raw:this.same(w,t)});
      }catch(e){
        rec.probes.push({name,status:"throw",spent:this.steps-before,error:e?.message??String(e),stop_status:e instanceof Stop?e.status:null});
      }
    }
    this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    try{
      this.budget=Math.min(snap.budget,snap.steps+100000);
      const x=this.whnf(a),y=this.whnf(b);
      rec.joint={left:shape(x),right:shape(y),same:this.same(x,y),spent:this.steps-snap.steps};
    }catch(e){
      rec.joint={error:e?.message??String(e),status:e instanceof Stop?e.status:null,spent:this.steps-snap.steps};
    }
    this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    console.log("LOCALDEF_FALLBACK_WHNF "+JSON.stringify(rec));
  }
  return retained.call(this,a,b,ctx);
};
const r=K.checkExport(row.input,caps,1_000_000);
proto.equal=retained;
console.log("LOCALDEF_FALLBACK_WHNF_RESULT "+JSON.stringify({hit,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed,frontier_declaration:r.frontier_declaration??null}));
