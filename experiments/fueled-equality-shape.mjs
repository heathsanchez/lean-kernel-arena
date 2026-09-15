import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

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
      rows.append({"name":"good/perf/fueled-chain.ndjson","input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}))[0];
if(!row)throw new Error("missing fueled-chain");

const proto=K.Kernel.prototype,retained=proto.equal;
const ids=new WeakMap();let nextId=1;
const id=x=>{
  if(x===null||typeof x!=="object")return typeof x+":"+String(x);
  let v=ids.get(x);if(v===undefined){v=nextId++;ids.set(x,v);}return "o"+v;
};
function shape(e){
  if(!Array.isArray(e))return typeof e;
  let h=e,n=0;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  if(n){
    if(Array.isArray(h)&&h[0]==="const")return "app:"+h[1]+":"+n;
    return "app:"+(h?.[0]??typeof h)+":"+n;
  }
  if(e[0]==="const")return "const:"+e[1];
  return e[0];
}
const pairs=new Map(),shapes=new Map();
let calls=0,success=0,failed=0,depth=0,maxDepth=0;
proto.equal=function(a,b,ctx=[]){
  calls++;depth++;maxDepth=Math.max(maxDepth,depth);
  const ka=id(a)+"|"+id(b)+"|"+ctx.length;
  let p=pairs.get(ka);if(!p){p={calls:0,success:0,failed:0,ticks:0,max:0,left:shape(a),right:shape(b),ctx:ctx.length};pairs.set(ka,p);}
  p.calls++;
  const sk=shape(a)+" -> "+shape(b)+" @"+ctx.length;
  let s=shapes.get(sk);if(!s){s={calls:0,success:0,failed:0,ticks:0,max:0};shapes.set(sk,s);}
  s.calls++;
  const before=this.steps;
  try{
    const out=retained.call(this,a,b,ctx);
    const d=this.steps-before;p.success++;p.ticks+=d;p.max=Math.max(p.max,d);s.success++;s.ticks+=d;s.max=Math.max(s.max,d);success++;
    return out;
  }catch(e){
    const d=this.steps-before;p.failed++;p.ticks+=d;p.max=Math.max(p.max,d);s.failed++;s.ticks+=d;s.max=Math.max(s.max,d);failed++;
    throw e;
  }finally{depth--;}
};
const r=K.checkExport(row.input,caps,1_000_000);
proto.equal=retained;

const topPairs=[...pairs.values()].sort((a,b)=>b.ticks-a.ticks||b.calls-a.calls).slice(0,30);
const repeatedPairs=[...pairs.values()].filter(x=>x.calls>1).sort((a,b)=>b.calls-a.calls||b.ticks-a.ticks).slice(0,30);
const topShapes=[...shapes.entries()].map(([shape,v])=>({shape,...v})).sort((a,b)=>b.ticks-a.ticks||b.calls-a.calls).slice(0,30);
console.log("FUELED_EQUALITY_SHAPE "+JSON.stringify({
 status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed,
 calls,success,failed,maxDepth,uniquePairs:pairs.size,repeatedPairCount:[...pairs.values()].filter(x=>x.calls>1).length,
 topPairs,repeatedPairs,topShapes
}));
