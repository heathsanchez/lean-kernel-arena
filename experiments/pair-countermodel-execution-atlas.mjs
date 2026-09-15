import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
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
wanted={"good/perf/magma-list-pair-n7.ndjson","good/perf/magma-list-pair-n21.ndjson"}
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and p in wanted:
      rows.append({"name":p,"expected":"ACCEPT","input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const focusRows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype,retainedRun=proto.run,retainedEqual=proto.equal,retainedWhnf=proto.whnf;
const stats={eqHits:0,eqStores:0,earlyPi:0,frontiers:0,projectionEligible:0,projectionSuccess:0,argChecks:0,whnfQueries:0,whnfHits:0,whnfStores:0,whnfCanonNodes:0,whnfLocalBypass:0};

function objectId(k,x){
  k.__pairIds??=new WeakMap();k.__pairNextId??=1;
  let id=k.__pairIds.get(x);if(id!==undefined)return id;
  id=k.__pairNextId++;k.__pairIds.set(x,id);return id;
}
function ctxKey(k,ctx){
  if(!ctx?.length)return "";
  return ctx.map(x=>(x!==null&&(typeof x==="object"||typeof x==="function"))?"o"+objectId(k,x):typeof x+":"+String(x)).join(",");
}
function eqSet(k,a,b){
  k.__pairEq??=new WeakMap();
  let m=k.__pairEq.get(a);if(!m){m=new WeakMap();k.__pairEq.set(a,m);}
  let s=m.get(b);if(!s){s=new Set();m.set(b,s);}return s;
}
function rawSpine(e){
  const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return{head:h,args};
}
function sameHead(k,a,b){return a===b||(Array.isArray(a)&&Array.isArray(b)&&k.same(a,b));}

const WHNF_END=Symbol("whnf-end");
function whnfEnsure(k){
  k.__pairWhnfWeak??=new WeakMap();k.__pairWhnfRoot??=new Map();k.__pairWhnfCache??=new WeakMap();
}
function whnfRep(k,e){
  if(!Array.isArray(e))return e;
  whnfEnsure(k);
  const old=k.__pairWhnfWeak.get(e);if(old!==undefined)return old;
  const xs=new Array(e.length);let changed=false;
  for(let i=0;i<e.length;i++){
    const y=Array.isArray(e[i])?whnfRep(k,e[i]):e[i];
    xs[i]=y;if(y!==e[i])changed=true;
  }
  let node=k.__pairWhnfRoot;
  for(const x of xs){
    let next=node.get(x);if(!(next instanceof Map)){next=new Map();node.set(x,next);}node=next;
  }
  let r=node.get(WHNF_END);
  if(r===undefined){r=changed?xs:e;node.set(WHNF_END,r);stats.whnfCanonNodes++;}
  k.__pairWhnfWeak.set(e,r);k.__pairWhnfWeak.set(r,r);return r;
}

function install(enabled){
  proto.run=retainedRun;proto.equal=retainedEqual;proto.whnf=retainedWhnf;
  if(!enabled)return;
  proto.run=function(...args){
    this.__pairEq=new WeakMap();this.__pairIds=new WeakMap();this.__pairNextId=1;
    this.__pairWhnfWeak=new WeakMap();this.__pairWhnfRoot=new Map();this.__pairWhnfCache=new WeakMap();
    return retainedRun.apply(this,args);
  };
  proto.whnf=function(e){
    if(this.localDefs===true || !Array.isArray(e)){
      if(this.localDefs===true)stats.whnfLocalBypass++;
      return retainedWhnf.call(this,e);
    }
    stats.whnfQueries++;
    const r=whnfRep(this,e);
    if(this.__pairWhnfCache?.has(r)){stats.whnfHits++;return this.__pairWhnfCache.get(r);}
    const out=retainedWhnf.call(this,e);
    this.__pairWhnfCache.set(r,out);stats.whnfStores++;
    return out;
  };
  proto.equal=function(a,b,ctx=[]){
    if(!Array.isArray(a)||!Array.isArray(b))return retainedEqual.call(this,a,b,ctx);
    const key=(this.localDefs?"L|":"N|")+ctxKey(this,ctx);
    const s=eqSet(this,a,b);
    if(s.has(key)){stats.eqHits++;return;}

    if(!this.localDefs&&a[0]==="pi"&&b[0]==="pi"){
      stats.earlyPi++;
      if(a===b||this.same(a,b)){s.add(key);eqSet(this,b,a).add(key);stats.eqStores++;return;}
      this.equal(a[1],b[1],ctx);
      this.equal(a[2],b[2],[...ctx,a[1]]);
      s.add(key);eqSet(this,b,a).add(key);stats.eqStores++;return;
    }

    try{
      const out=retainedEqual.call(this,a,b,ctx);
      s.add(key);eqSet(this,b,a).add(key);stats.eqStores++;
      return out;
    }catch(original){
      if((this._pairProjectionDepth??0)>0 || !(original instanceof Stop) ||
         original.status!==UNKNOWN || original.message!=="conversion-frontier")
        throw original;
      stats.frontiers++;
      const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
      try{
        const x=this.normal(a),y=this.normal(b);
        if(!Array.isArray(x)||!Array.isArray(y)||x[0]!=="proj"||y[0]!=="proj"||
           x[1]!==y[1]||x[2]!==y[2])throw original;
        const sx=rawSpine(x[3]),sy=rawSpine(y[3]);
        if(!sx.args.length||sx.args.length!==sy.args.length||!sameHead(this,sx.head,sy.head)||sx.head?.[0]!=="const")throw original;
        const d=this.env.get(sx.head[1]);if(d?.kind!=="rec")throw original;
        stats.projectionEligible++;
        this._pairProjectionDepth=1;
        const order=sx.args.map((_,i)=>i).sort((i,j)=>{
          const ai=sx.args[i]===sy.args[i]||this.same(sx.args[i],sy.args[i])?0:1;
          const aj=sx.args[j]===sy.args[j]||this.same(sx.args[j],sy.args[j])?0:1;
          return ai-aj;
        });
        for(const i of order){
          if(sx.args[i]===sy.args[i]||this.same(sx.args[i],sy.args[i]))continue;
          stats.argChecks++;
          this.equal(sx.args[i],sy.args[i],ctx);
        }
        this._pairProjectionDepth=0;
        stats.projectionSuccess++;
        s.add(key);eqSet(this,b,a).add(key);stats.eqStores++;
        return;
      }catch(e){
        this._pairProjectionDepth=0;
        if(e===original||e instanceof Stop||e instanceof RangeError){
          this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
          throw original;
        }
        throw e;
      }
    }
  };
}


const atlas={
  active:false,stack:[],leaf:{},outer:{},methodCalls:{},
  inferIds:new WeakMap(),inferNext:1,inferTerms:new Map()
};
const atlasMethods=[
  "validate","sortOf","infer","equal","normal","proofType","whnf","substitute","shift",
  "instantiateDeclaration","getApp","same","make","inferProjection","addSingleInductive"
];
function inCountermodel(k){
  return typeof k?.currentDeclaration==="string" && k.currentDeclaration.includes("countermodel");
}
function termDesc(e){
  if(!Array.isArray(e)) return {kind:typeof e};
  let h=e,args=0;
  while(Array.isArray(h)&&h[0]==="app"){args++;h=h[1];}
  return {
    tag:e[0],app_spine:args,
    head_tag:Array.isArray(h)?h[0]:typeof h,
    head_const:Array.isArray(h)&&h[0]==="const"?h[1]:null
  };
}
function inferRecord(k,e){
  if(!Array.isArray(e))return;
  let id=atlas.inferIds.get(e);
  if(id===undefined){
    id=atlas.inferNext++;atlas.inferIds.set(e,id);
    atlas.inferTerms.set(id,{id,count:0,...termDesc(e)});
  }
  atlas.inferTerms.get(id).count++;
}
function wrapAtlas(){
  const originals=new Map();
  const tick0=proto.tick;
  originals.set("tick",tick0);
  proto.tick=function(...args){
    if(inCountermodel(this)){
      const leaf=atlas.stack.length?atlas.stack[atlas.stack.length-1]:"run-other";
      const outer=atlas.stack.length?atlas.stack[0]:"run-other";
      atlas.leaf[leaf]=(atlas.leaf[leaf]??0)+1;
      atlas.outer[outer]=(atlas.outer[outer]??0)+1;
    }
    return tick0.apply(this,args);
  };
  for(const name of atlasMethods){
    const fn=proto[name];
    if(typeof fn!=="function")continue;
    originals.set(name,fn);
    proto[name]=function(...args){
      const active=inCountermodel(this);
      if(active){
        atlas.methodCalls[name]=(atlas.methodCalls[name]??0)+1;
        if(name==="infer")inferRecord(this,args[0]);
        atlas.stack.push(name);
      }
      try{return fn.apply(this,args);}
      finally{if(active)atlas.stack.pop();}
    };
  }
  return ()=>{
    proto.tick=originals.get("tick");
    for(const [name,fn] of originals)if(name!=="tick")proto[name]=fn;
  };
}
function atlasSnapshot(){
  const rank=o=>Object.entries(o).sort((a,b)=>b[1]-a[1]).map(([operation,count])=>({operation,count}));
  const topInfer=[...atlas.inferTerms.values()].sort((a,b)=>b.count-a.count).slice(0,30);
  return {leaf:rank(atlas.leaf),outer:rank(atlas.outer),methodCalls:rank(atlas.methodCalls),topInfer};
}
function evaluate(budget,enabled,rows){
  install(enabled);
  atlas.stack=[];atlas.leaf={};atlas.outer={};atlas.methodCalls={};
  atlas.inferIds=new WeakMap();atlas.inferNext=1;atlas.inferTerms=new Map();
  const restoreAtlas=enabled?wrapAtlas():()=>{};
  const before={...stats},results=[];let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null});
  }
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  const declaration_atlas=enabled?atlasSnapshot():null;restoreAtlas();
  return {budget,enabled,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results,declaration_atlas};
}
const thresholds=[];
for(const budget of [1000000]){
  thresholds.push(evaluate(budget,true,focusRows));
}
install(false);
console.log("PAIR_COUNTERMODEL_EXECUTION_ATLAS_THRESHOLDS "+JSON.stringify(thresholds));

console.log("PAIR_COUNTERMODEL_EXECUTION_ATLAS "+JSON.stringify(thresholds));
process.exit(0);
