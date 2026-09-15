import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
if(createHash("sha256").update(data).digest("hex")!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read(); row=None
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.endswith("good/perf/beta-ladder.ndjson"):
      row={"name":m.name,"input":a.extractfile(m).read().decode("utf-8")};break
print(json.dumps(row))
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(!row) throw new Error("beta-ladder missing");

const proto=K.Kernel.prototype, retained=proto.substitute;
const seenBodies=new WeakSet(),seenArgs=new WeakSet(),pairs=new WeakMap();
let uniqueBodies=0,uniqueArgs=0,pairHits=0,pairStores=0;
const stats={calls:0,totalSemanticCost:0,totalAllocCost:0,totalBodyNodes:0,totalArgNodes:0,
  binderAbsent:0,binderOnce:0,binderTwice:0,binderMany:0,localDefCalls:0};
const top=[];

function size(e){
  if(!Array.isArray(e)) return 0;
  let n=0,stack=[e];
  while(stack.length){
    const x=stack.pop(); if(!Array.isArray(x)) continue;
    n++;
    if(x[0]==="proj"){stack.push(x[3]);continue;}
    for(let i=1;i<x.length;i++) if(Array.isArray(x[i])) stack.push(x[i]);
  }
  return n;
}
function occurrences(root,targetDepth){
  if(!Array.isArray(root)) return 0;
  let count=0,stack=[{e:root,depth:targetDepth}];
  while(stack.length){
    const {e,depth}=stack.pop();
    if(!Array.isArray(e)) continue;
    switch(e[0]){
      case "var": if(e[1]===depth) count++; break;
      case "pi": case "lam":
        stack.push({e:e[1],depth}); stack.push({e:e[2],depth:depth+1}); break;
      case "let":
        stack.push({e:e[1],depth}); stack.push({e:e[2],depth}); stack.push({e:e[3],depth:depth+1}); break;
      case "proj": stack.push({e:e[3],depth}); break;
      default:
        for(let i=1;i<e.length;i++) if(Array.isArray(e[i])) stack.push({e:e[i],depth});
    }
  }
  return count;
}
function pairSeen(body,arg){
  if(!Array.isArray(body)||!Array.isArray(arg)) return false;
  let s=pairs.get(body); if(!s){s=new WeakSet();pairs.set(body,s);}
  if(s.has(arg)){pairHits++;return true;}
  s.add(arg);pairStores++;return false;
}
function insertTop(x){
  top.push(x); top.sort((a,b)=>b.semanticCost-a.semanticCost); if(top.length>30) top.length=30;
}

proto.substitute=function(e,arg,depth=0){
  if(this.__betaSubProfileDepth) return retained.call(this,e,arg,depth);
  this.__betaSubProfileDepth=1;
  const bodyNodes=size(e),argNodes=size(arg),occ=occurrences(e,depth);
  if(Array.isArray(e)&&!seenBodies.has(e)){seenBodies.add(e);uniqueBodies++;}
  if(Array.isArray(arg)&&!seenArgs.has(arg)){seenArgs.add(arg);uniqueArgs++;}
  const repeatedPair=pairSeen(e,arg),beforeSteps=this.steps,beforeAlloc=this.allocations??0;
  stats.calls++; stats.totalBodyNodes+=bodyNodes; stats.totalArgNodes+=argNodes;
  if(this.localDefs===true) stats.localDefCalls++;
  if(occ===0)stats.binderAbsent++; else if(occ===1)stats.binderOnce++; else if(occ===2)stats.binderTwice++; else stats.binderMany++;
  try{
    const out=retained.call(this,e,arg,depth);
    const semanticCost=this.steps-beforeSteps,allocCost=(this.allocations??0)-beforeAlloc;
    stats.totalSemanticCost+=semanticCost; stats.totalAllocCost+=allocCost;
    insertTop({semanticCost,allocCost,bodyNodes,argNodes,occurrences:occ,depth,repeatedPair,
      bodyTag:Array.isArray(e)?e[0]:typeof e,argTag:Array.isArray(arg)?arg[0]:typeof arg,
      localDefs:this.localDefs===true,currentDeclaration:this.currentDeclaration??null});
    return out;
  } finally { this.__betaSubProfileDepth=0; }
};

const t0=Date.now();
const r=K.checkExport(row.input,caps,1_000_000);
proto.substitute=retained;
console.log("BETA_SUBSTITUTION_SHAPE "+JSON.stringify({
  name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
  stats:{...stats,uniqueBodies,uniqueArgs,pairHits,pairStores},top
}));
