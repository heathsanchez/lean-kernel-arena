// Exclusive semantic-step profiler for the post-proof magma frontier.
// The projection retry is the already-falsified/diagnostic execution change:
// it is used only to move past the two confirmed proof-irrelevance frontiers.
// No profile counter changes semantic steps.
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
if(rows.length!==2) throw new Error("missing magma rows");

const proto=K.Kernel.prototype;
const baseEqual=proto.equal,baseNormal=proto.normal,baseTick=proto.tick;
let retryStats=null;

function sameData(a,b){
  if(a===b) return true;
  const w=[[a,b]];
  while(w.length){
    const [x,y]=w.pop();
    if(x===y) continue;
    if(!Array.isArray(x)||!Array.isArray(y)||x.length!==y.length) return false;
    for(let i=0;i<x.length;i++){
      if(x[i]===y[i]) continue;
      if(Array.isArray(x[i])&&Array.isArray(y[i])) w.push([x[i],y[i]]);
      else return false;
    }
  }
  return true;
}
function comparePaid(k,x,y,ctx){
  const w=[{a:x,b:y,ctx}];
  while(w.length){
    const {a:u,b:v,ctx:c}=w.pop();
    if(u===v) continue;
    k.tick();
    if(!Array.isArray(u)||!Array.isArray(v)){baseEqual.call(k,u,v,c);continue;}
    if(u[0]!==v[0]||u.length!==v.length){baseEqual.call(k,u,v,c);continue;}
    switch(u[0]){
      case "var":
        if(u[1]!==v[1]){
          retryStats.varMismatches++;
          const tu=k.proofType(u,c),tv=k.proofType(v,c);
          if(tu!==null&&tv!==null){
            retryStats.proofDischarges++;
            if(!k.same(tu,tv)) baseEqual.call(k,tu,tv,c);
          }else baseEqual.call(k,u,v,c);
        }
        break;
      case "nat": case "strlit":
        if(u[1]!==v[1]) baseEqual.call(k,u,v,c); break;
      case "sort":
        if(!sameData(u[1],v[1])) baseEqual.call(k,u,v,c); break;
      case "const":
        if(u[1]!==v[1]||!sameData(u[2]??[],v[2]??[])) baseEqual.call(k,u,v,c); break;
      case "app":
        w.push({a:u[2],b:v[2],ctx:c}); w.push({a:u[1],b:v[1],ctx:c}); break;
      case "pi": case "lam":
        w.push({a:u[2],b:v[2],ctx:[...c,u[1]]}); w.push({a:u[1],b:v[1],ctx:c}); break;
      case "proj":
        if(u[1]!==v[1]||u[2]!==v[2]) baseEqual.call(k,u,v,c);
        else w.push({a:u[3],b:v[3],ctx:c});
        break;
      default: baseEqual.call(k,u,v,c);
    }
  }
}
proto.normal=function(e){
  this.__paidNormals??=new WeakMap();
  const out=baseNormal.call(this,e);
  if(Array.isArray(e)) this.__paidNormals.set(e,out);
  return out;
};
proto.equal=function(a,b,ctx=[]){
  const frontierBefore=this.conversionFrontier;
  try{return baseEqual.call(this,a,b,ctx);}
  catch(err){
    if(err?.message!=="conversion-frontier"||!Array.isArray(a)||!Array.isArray(b)||
       a[0]!=="proj"||b[0]!=="proj"||a[1]!==b[1]||a[2]!==b[2]) throw err;
    const x=this.__paidNormals?.get(a),y=this.__paidNormals?.get(b);
    if(!x||!y) throw err;
    retryStats.attempts++;
    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    try{
      comparePaid(this,x,y,ctx); retryStats.successes++;
      this.conversionFrontier=frontierBefore; return;
    }catch(retry){
      retryStats.failures++;
      this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
      throw err;
    }
  }
};

// Wrap final retained methods and attribute each semantic tick to the innermost
// selected method active when that tick occurs.
const names=["validate","infer","sortOf","equal","normal","whnf","substitute","shift","same",
  "make","instantiateDeclaration","proofType","getApp","hasConst","structureEtaMatches","functionEtaContract"];
const originals=new Map();
const counts=new Map();
function add(key,method){
  let m=counts.get(key); if(!m){m=new Map();counts.set(key,m);}
  m.set(method,(m.get(method)??0)+1);
}
for(const name of names){
  if(typeof proto[name]!=="function") continue;
  const old=proto[name]; originals.set(name,old);
  proto[name]=function(...args){
    this.__profStack??=[];
    this.__profStack.push(name);
    try{return old.apply(this,args);}
    finally{this.__profStack.pop();}
  };
}
proto.tick=function(...args){
  const out=baseTick.apply(this,args);
  const mode=this.localDefs?"local":"retained";
  const decl=this.currentDeclaration??"<none>";
  const method=this.__profStack?.at(-1)??"<unwrapped>";
  add(mode+"|"+decl,method);
  return out;
};

function summarize(){
  const rows=[];
  for(const [key,m] of counts){
    const [mode,...rest]=key.split("|"),decl=rest.join("|");
    const methods=[...m].sort((a,b)=>b[1]-a[1]);
    rows.push({mode,decl,total:methods.reduce((s,x)=>s+x[1],0),methods:methods.slice(0,12)});
  }
  rows.sort((a,b)=>b.total-a.total);
  return {
    topDeclarations:rows.slice(0,12),
    countermodel:rows.filter(r=>r.decl.includes("countermodel")).slice(0,8)
  };
}

const results=[];
for(const row of rows){
  counts.clear(); retryStats={attempts:0,successes:0,failures:0,varMismatches:0,proofDischarges:0};
  const r=K.checkExport(row.input,caps,2_000_000);
  results.push({name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
    retries:{...retryStats},profile:summarize()});
}
for(const [name,old] of originals) proto[name]=old;
proto.equal=baseEqual;proto.normal=baseNormal;proto.tick=baseTick;
console.log("MAGMA_COUNTERMODEL_PROFILE "+JSON.stringify({arena_sha256:sha,budget:2000000,results}));
