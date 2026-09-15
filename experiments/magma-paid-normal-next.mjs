// Diagnostic continuation after the first magma projection frontier.
// Reuse already-paid normal forms, discharge differing proof variables directly
// by the retained proof-irrelevance rule, and report the next exact obstruction.
import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
want={"good/perf/magma-list-pair-n7.ndjson","good/perf/magma-list-pair-n21.ndjson"}
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and p in want:
      rows.append({"name":p,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(sorted(rows,key=lambda x:x["name"])))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==2) throw new Error("missing magma pair rows");

const proto=K.Kernel.prototype;
const retainedEqual=proto.equal,retainedNormal=proto.normal;
let stats=null;

function sameData(a,b){
  if(a===b) return true;
  const work=[[a,b]];
  while(work.length){
    const [x,y]=work.pop();
    if(x===y) continue;
    if(!Array.isArray(x)||!Array.isArray(y)||x.length!==y.length) return false;
    for(let i=0;i<x.length;i++){
      if(x[i]===y[i]) continue;
      if(Array.isArray(x[i])&&Array.isArray(y[i])) work.push([x[i],y[i]]);
      else return false;
    }
  }
  return true;
}

function comparePaid(kernel,x,y,ctx){
  const work=[{a:x,b:y,ctx}];
  while(work.length){
    const f=work.pop(),u=f.a,v=f.b,c=f.ctx;
    if(u===v) continue;
    stats.frames++;
    kernel.tick();
    if(!Array.isArray(u)||!Array.isArray(v)){ retainedEqual.call(kernel,u,v,c); continue; }
    if(u[0]!==v[0]||u.length!==v.length){ retainedEqual.call(kernel,u,v,c); continue; }
    switch(u[0]){
      case "var":
        if(u[1]!==v[1]){
          stats.varMismatches++;
          const tu=kernel.proofType(u,c),tv=kernel.proofType(v,c);
          if(tu!==null&&tv!==null){
            stats.proofPairs++;
            if(!kernel.same(tu,tv)) retainedEqual.call(kernel,tu,tv,c);
            stats.proofDischarges++;
          }else retainedEqual.call(kernel,u,v,c);
        }
        break;
      case "nat":
      case "strlit":
        if(u[1]!==v[1]) retainedEqual.call(kernel,u,v,c);
        break;
      case "sort":
        if(!sameData(u[1],v[1])) retainedEqual.call(kernel,u,v,c);
        break;
      case "const":
        if(u[1]!==v[1]||!sameData(u[2]??[],v[2]??[])) retainedEqual.call(kernel,u,v,c);
        break;
      case "app":
        work.push({a:u[2],b:v[2],ctx:c});
        work.push({a:u[1],b:v[1],ctx:c});
        break;
      case "pi":
      case "lam":
        work.push({a:u[2],b:v[2],ctx:[...c,u[1]]});
        work.push({a:u[1],b:v[1],ctx:c});
        break;
      case "proj":
        if(u[1]!==v[1]||u[2]!==v[2]) retainedEqual.call(kernel,u,v,c);
        else work.push({a:u[3],b:v[3],ctx:c});
        break;
      default:
        retainedEqual.call(kernel,u,v,c);
    }
  }
}

proto.normal=function(e){
  this.__paidNormals ??= new WeakMap();
  const out=retainedNormal.call(this,e);
  if(Array.isArray(e)) this.__paidNormals.set(e,out);
  return out;
};

proto.equal=function(a,b,ctx=[]){
  const frontierBefore=this.conversionFrontier;
  try{return retainedEqual.call(this,a,b,ctx);}
  catch(err){
    if(err?.message!=="conversion-frontier"||!Array.isArray(a)||!Array.isArray(b)||
       a[0]!=="proj"||b[0]!=="proj"||a[1]!==b[1]||a[2]!==b[2]) throw err;
    const x=this.__paidNormals?.get(a),y=this.__paidNormals?.get(b);
    if(!x||!y) throw err;
    stats.attempts++;
    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    try{
      comparePaid(this,x,y,ctx);
      stats.successes++;
      this.conversionFrontier=frontierBefore;
      return;
    }catch(retry){
      stats.failures++;
      stats.lastRetryReason=retry?.message??retry?.name??String(retry);
      this.steps=snap.steps; this.budget=snap.budget; this.conversionFrontier=snap.frontier;
      throw err;
    }
  }
};

const budgets=[1_000_000,1_500_000,2_000_000,3_000_000,5_000_000];
const out=[];
for(const row of rows){
  for(const budget of budgets){
    stats={attempts:0,successes:0,failures:0,frames:0,varMismatches:0,proofPairs:0,proofDischarges:0,lastRetryReason:null};
    const r=K.checkExport(row.input,caps,budget);
    out.push({name:row.name,budget,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier:r.conversion_frontier??r.frontier_declaration??null,stats:{...stats}});
    if(r.status!=="UNKNOWN") break;
  }
}
proto.equal=retainedEqual; proto.normal=retainedNormal;
console.log("MAGMA_PAID_NORMAL_NEXT "+JSON.stringify({arena_sha256:sha,results:out}));
