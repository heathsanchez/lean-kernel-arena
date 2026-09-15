// Focused orthogonal separator for the two post-proof magma bottlenecks.
// MODE=retry|proof|getapp|both. Every mode includes the already-diagnosed
// same-projection paid-normal retry so the two confirmed proof-variable
// frontiers do not mask the resource experiment.
//
// proof: compile exact completed proofType(term, exact context, exact params).
// getapp: compile exact completed application-spine decomposition by term identity.
// Neither cache stores throws/frontiers/failures; hits repay zero semantic work.
import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const MODE=process.env.MODE??"both";
if(!["retry","proof","getapp","both","same","getapp-same","proof-same","all"].includes(MODE)) throw new Error("bad MODE "+MODE);
const useProof=["proof","both","proof-same","all"].includes(MODE);
const useGetApp=["getapp","both","getapp-same","all"].includes(MODE);
const useSame=["same","getapp-same","proof-same","all"].includes(MODE);

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
const retainedRun=proto.run;
const retainedProofType=proto.proofType;
const retainedGetApp=proto.getApp;
const retainedSame=proto.same;
const retainedEqual=proto.equal;
const retainedNormal=proto.normal;

const stats={
  proof:{queries:0,hits:0,storesProof:0,storesNonProof:0},
  getapp:{queries:0,hits:0,stores:0},
  same:{queries:0,hits:0,storesTrue:0,storesFalse:0},
  retry:{attempts:0,successes:0,failures:0,varMismatches:0,proofDischarges:0}
};

function objectId(k,x){
  k.__pcIds??=new WeakMap(); k.__pcNextId??=1;
  let id=k.__pcIds.get(x);
  if(id!==undefined) return id;
  id=k.__pcNextId++; k.__pcIds.set(x,id); return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length) return "";
  return ctx.map(x=>(x!==null&&(typeof x==="object"||typeof x==="function"))
    ?"o"+objectId(k,x):typeof x+":"+String(x)).join(",");
}
function paramsKey(k){return [...(k.params??[])].sort().join("\u0000");}

proto.run=function(...args){
  this.__proofTypeCache=new WeakMap();
  this.__getAppCache=new WeakMap();
  this.__sameCache=new WeakMap();
  this.__pcIds=new WeakMap();
  this.__pcNextId=1;
  this.__paidNormals=new WeakMap();
  return retainedRun.apply(this,args);
};

if(useProof){
  proto.proofType=function(e,ctx=[]){
    stats.proof.queries++;
    if(!Array.isArray(e)) return retainedProofType.call(this,e,ctx);
    this.__proofTypeCache??=new WeakMap();
    let byKey=this.__proofTypeCache.get(e);
    if(!byKey){byKey=new Map();this.__proofTypeCache.set(e,byKey);}
    const key=paramsKey(this)+"|"+ctxKey(this,ctx);
    if(byKey.has(key)){stats.proof.hits++;return byKey.get(key);}
    const out=retainedProofType.call(this,e,ctx);
    byKey.set(key,out);
    if(out===null) stats.proof.storesNonProof++; else stats.proof.storesProof++;
    return out;
  };
}
if(useSame){
  proto.same=function(a,b){
    stats.same.queries++;
    if(!Array.isArray(a)||!Array.isArray(b)) return retainedSame.call(this,a,b);
    this.__sameCache??=new WeakMap();
    let byRight=this.__sameCache.get(a);
    if(!byRight){byRight=new WeakMap();this.__sameCache.set(a,byRight);}
    if(byRight.has(b)){stats.same.hits++;return byRight.get(b);}
    const out=retainedSame.call(this,a,b);
    byRight.set(b,out);
    let reverse=this.__sameCache.get(b);
    if(!reverse){reverse=new WeakMap();this.__sameCache.set(b,reverse);}
    reverse.set(a,out);
    if(out) stats.same.storesTrue++; else stats.same.storesFalse++;
    return out;
  };
}
if(useGetApp){
  proto.getApp=function(e){
    stats.getapp.queries++;
    if(!Array.isArray(e)) return retainedGetApp.call(this,e);
    this.__getAppCache??=new WeakMap();
    if(this.__getAppCache.has(e)){stats.getapp.hits++;return this.__getAppCache.get(e);}
    const out=retainedGetApp.call(this,e);
    this.__getAppCache.set(e,out);stats.getapp.stores++;
    return out;
  };
}

proto.normal=function(e){
  const out=retainedNormal.call(this,e);
  if(Array.isArray(e)){this.__paidNormals??=new WeakMap();this.__paidNormals.set(e,out);}
  return out;
};

function sameData(a,b){
  if(a===b)return true;
  const work=[[a,b]];
  while(work.length){
    const [x,y]=work.pop();
    if(x===y)continue;
    if(!Array.isArray(x)||!Array.isArray(y)||x.length!==y.length)return false;
    for(let i=0;i<x.length;i++){
      if(x[i]===y[i])continue;
      if(Array.isArray(x[i])&&Array.isArray(y[i]))work.push([x[i],y[i]]);
      else return false;
    }
  }
  return true;
}
function comparePaid(k,x,y,ctx){
  const work=[{a:x,b:y,ctx}];
  while(work.length){
    const {a:u,b:v,ctx:c}=work.pop();
    if(u===v)continue;
    k.tick();
    if(!Array.isArray(u)||!Array.isArray(v)){retainedEqual.call(k,u,v,c);continue;}
    if(u[0]!==v[0]||u.length!==v.length){retainedEqual.call(k,u,v,c);continue;}
    switch(u[0]){
      case "var":
        if(u[1]!==v[1]){
          stats.retry.varMismatches++;
          const tu=k.proofType(u,c),tv=k.proofType(v,c);
          if(tu!==null&&tv!==null){
            if(!k.same(tu,tv))retainedEqual.call(k,tu,tv,c);
            stats.retry.proofDischarges++;
          }else retainedEqual.call(k,u,v,c);
        }
        break;
      case "nat": case "strlit":
        if(u[1]!==v[1])retainedEqual.call(k,u,v,c);break;
      case "sort":
        if(!sameData(u[1],v[1]))retainedEqual.call(k,u,v,c);break;
      case "const":
        if(u[1]!==v[1]||!sameData(u[2]??[],v[2]??[]))retainedEqual.call(k,u,v,c);break;
      case "app":
        work.push({a:u[2],b:v[2],ctx:c});work.push({a:u[1],b:v[1],ctx:c});break;
      case "pi": case "lam":
        work.push({a:u[2],b:v[2],ctx:[...c,u[1]]});work.push({a:u[1],b:v[1],ctx:c});break;
      case "proj":
        if(u[1]!==v[1]||u[2]!==v[2])retainedEqual.call(k,u,v,c);
        else work.push({a:u[3],b:v[3],ctx:c});
        break;
      default:retainedEqual.call(k,u,v,c);
    }
  }
}
proto.equal=function(a,b,ctx=[]){
  const frontierBefore=this.conversionFrontier;
  try{return retainedEqual.call(this,a,b,ctx);}
  catch(err){
    if(err?.message!=="conversion-frontier"||!Array.isArray(a)||!Array.isArray(b)||
       a[0]!=="proj"||b[0]!=="proj"||a[1]!==b[1]||a[2]!==b[2])throw err;
    const x=this.__paidNormals?.get(a),y=this.__paidNormals?.get(b);
    if(!x||!y)throw err;
    stats.retry.attempts++;
    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    try{
      comparePaid(this,x,y,ctx);
      stats.retry.successes++;
      this.conversionFrontier=frontierBefore;
      return;
    }catch(retry){
      stats.retry.failures++;
      this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
      throw err;
    }
  }
};

const results=[];
for(const row of rows){
  const before=JSON.parse(JSON.stringify(stats));
  const t0=Date.now();
  const r=K.checkExport(row.input,caps,1_000_000);
  const after=JSON.parse(JSON.stringify(stats));
  function delta(a,b){
    const o={};
    for(const k of Object.keys(b)){
      if(typeof b[k]==="object")o[k]=delta(a[k],b[k]);
      else o[k]=b[k]-a[k];
    }
    return o;
  }
  results.push({name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
    frontier_declaration:r.frontier_declaration??null,stats:delta(before,after)});
}
proto.run=retainedRun;proto.proofType=retainedProofType;proto.getApp=retainedGetApp;proto.same=retainedSame;
proto.equal=retainedEqual;proto.normal=retainedNormal;
console.log("EXACT_CONSEQUENCE_FOCUS "+JSON.stringify({mode:MODE,arena_sha256:sha,budget:1000000,results}));
