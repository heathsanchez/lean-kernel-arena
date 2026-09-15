import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop,UNKNOWN} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const scopeMode="support";
if(!["closed","support"].includes(scopeMode))throw new Error("bad scope mode "+scopeMode);
const expectedHash="0cdb181ce17bc4f685beea8d3ccb90675ecc029cae9c4dc86629d2adbcb6e8dd";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed: got "+sha+" expected "+expectedHash);
const py=String.raw`
import io,tarfile,json,sys
wanted={"good/perf/magma-list-pair-n7.ndjson"}
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and p in wanted:
      rows.append({"name":p,"expected":"ACCEPT","input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const focusRows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype,retainedRun=proto.run,retainedEqual=proto.equal,retainedWhnf=proto.whnf,retainedNormal=proto.normal,retainedSubstitute=proto.substitute,retainedTick=proto.tick;
const stats={eqHits:0,eqStores:0,earlyPi:0,frontiers:0,projectionEligible:0,projectionSuccess:0,argChecks:0,whnfQueries:0,whnfHits:0,whnfStores:0,whnfCanonNodes:0,whnfLocalBypass:0,deepNormalCalls:0,deepNormalVisits:0,deepNormalHits:0,deepNormalReducedHits:0,deepNormalStores:0,deepNormalBuilds:0,deepNormalCtxKeys:0,deepNormalEntries:0,supportClosed:0,supportDependent:0,supportMax:0,supportKeyShrink:0};
const subAtlas={start:2000000,calls:0,returns:0,states:new Map(),rootIds:new WeakMap(),argIds:new WeakMap(),nextId:1};
function subId(map,x){
  if(!Array.isArray(x))return typeof x+":"+String(x);
  let id=map.get(x);if(id!==undefined)return id;
  id=subAtlas.nextId++;map.set(x,id);return id;
}
function termShape(e){
  if(!Array.isArray(e))return {tag:typeof e,bytes:String(e).length};
  const raw=JSON.stringify(e);
  return {tag:e[0],bytes:raw.length,preview:raw.slice(0,700)};
}
function subReset(){
  subAtlas.calls=0;subAtlas.returns=0;subAtlas.states=new Map();
  subAtlas.rootIds=new WeakMap();subAtlas.argIds=new WeakMap();subAtlas.nextId=1;
}
function subRecord(k,root,arg,depth){
  if((k.steps??0)<subAtlas.start)return null;
  subAtlas.calls++;
  const key=subId(subAtlas.rootIds,root)+"|"+subId(subAtlas.argIds,arg)+"|"+depth;
  let x=subAtlas.states.get(key);
  if(!x){
    x={key,calls:0,returns:0,root:termShape(root),arg:termShape(arg),depth,firstStep:k.steps,lastStep:k.steps};
    subAtlas.states.set(key,x);
  }
  x.calls++;x.lastStep=k.steps;
  return key;
}
function subReturned(key,out){
  if(key===null)return;
  const x=subAtlas.states.get(key);if(!x)return;
  x.returns++;subAtlas.returns++;
  if(!x.output)x.output=termShape(out);
}
function subSummary(){
  return {
    start:subAtlas.start,calls:subAtlas.calls,returns:subAtlas.returns,uniqueStates:subAtlas.states.size,
    top:[...subAtlas.states.values()].sort((a,b)=>b.calls-a.calls).slice(0,40)
  };
}



const tailAtlas={start:2000000,counts:new Map(),samples:new Map()};
const atlasNames=["validate","sortOf","infer","equal","normal","proofType","whnf","substitute","shift","instantiateDeclaration","getApp","same","make","inferProjection","structureEtaMatches","functionEtaContract","isUnitLikeType"];
function atlasReset(){tailAtlas.counts=new Map();tailAtlas.samples=new Map();}
function atlasWrap(){
  const saved=new Map();
  proto.tick=function(...args){
    if((this.steps??0)>=tailAtlas.start){
      const st=this.__rgTailStack,tag=st?.length?st[st.length-1]:"run-other";
      tailAtlas.counts.set(tag,(tailAtlas.counts.get(tag)??0)+1);
    }
    return retainedTick.apply(this,args);
  };
  for(const name of atlasNames){
    const fn=proto[name];if(typeof fn!=="function")continue;
    saved.set(name,fn);
    proto[name]=function(...args){
      this.__rgTailStack??=[];this.__rgTailStack.push(name);
      try{return fn.apply(this,args);}
      finally{this.__rgTailStack.pop();}
    };
  }
  return ()=>{
    for(const [name,fn] of saved)proto[name]=fn;
    proto.tick=retainedTick;
  };
}
function atlasSummary(){
  const ranked=[...tailAtlas.counts.entries()].sort((a,b)=>b[1]-a[1]);
  const total=ranked.reduce((n,x)=>n+x[1],0);
  return {start:tailAtlas.start,total,operations:ranked.map(([operation,count])=>({operation,count,fraction:total?count/total:0}))};
}

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


function deepNormObjectId(k,x){
  k.__deepNormIds??=new WeakMap();k.__deepNormNextId??=1;
  if(x===null || (typeof x!=="object"&&typeof x!=="function"))return typeof x+":"+String(x);
  let id=k.__deepNormIds.get(x);
  if(id!==undefined)return "o"+id;
  id=k.__deepNormNextId++;k.__deepNormIds.set(x,id);return "o"+id;
}
function freeNeed(k,e,depth=0){
  if(!Array.isArray(e))return 0;
  k.__freeNeed??=new WeakMap();
  if(depth===0&&k.__freeNeed.has(e))return k.__freeNeed.get(e);
  let out=0;
  switch(e[0]){
    case "var": out=e[1]<depth?0:e[1]-depth+1; break;
    case "sort": case "const": case "nat": case "strlit": out=0; break;
    case "proj": out=freeNeed(k,e[3],depth); break;
    case "pi": case "lam":
      out=Math.max(freeNeed(k,e[1],depth),freeNeed(k,e[2],depth+1)); break;
    case "let":
      out=Math.max(freeNeed(k,e[1],depth),freeNeed(k,e[2],depth),freeNeed(k,e[3],depth+1)); break;
    default:
      for(let i=1;i<e.length;i++)out=Math.max(out,freeNeed(k,e[i],depth));
  }
  if(depth===0)k.__freeNeed.set(e,out);
  return out;
}
function deepNormCtxKey(k,ctx,e){
  stats.deepNormalCtxKeys++;
  const need=freeNeed(k,e,0);
  stats.supportMax=Math.max(stats.supportMax,need);
  if(need===0){stats.supportClosed++;return "C";}
  stats.supportDependent++;
  if(scopeMode==="closed"){
    const parts=new Array(ctx.length);
    for(let i=0;i<ctx.length;i++){
      const x=ctx[i];
      if(x?.__localDef===true){
        stats.deepNormalEntries++;
        parts[i]="D:"+deepNormObjectId(k,x.type)+":"+deepNormObjectId(k,x.value);
      }else parts[i]="T:"+deepNormObjectId(k,x);
    }
    return parts.join("|");
  }
  const n=Math.min(need,ctx?.length??0),start=(ctx?.length??0)-n;
  if(start>0)stats.supportKeyShrink++;
  const parts=[];
  for(let i=start;i<(ctx?.length??0);i++){
    const x=ctx[i];
    if(x?.__localDef===true){
      stats.deepNormalEntries++;
      parts.push("D:"+deepNormObjectId(k,x.type)+":"+deepNormObjectId(k,x.value));
    }else parts.push("T");
  }
  return "S"+need+"|"+parts.join("|");
}
function deepNormSlot(k,e,key){
  if(!Array.isArray(e))return null;
  k.__deepNormCache??=new WeakMap();
  let byCtx=k.__deepNormCache.get(e);
  if(!(byCtx instanceof Map)){byCtx=new Map();k.__deepNormCache.set(e,byCtx);}
  return {
    has:()=>byCtx.has(key),
    get:()=>byCtx.get(key),
    set:v=>{byCtx.set(key,v);stats.deepNormalStores++;}
  };
}
function scopedWhnf(k,e,ctx){
  if(k.localDefs===true && typeof k.withCtx==="function")
    return k.withCtx(ctx,()=>retainedWhnf.call(k,e));
  return retainedWhnf.call(k,e);
}
function deepLocalNormal(k,root){
  stats.deepNormalCalls++;
  if(!Array.isArray(root))return root;
  const rootCtx=k._activeCtx??[];
  const work=[{kind:"visit",e:root,ctx:rootCtx}],vals=[];
  while(work.length){
    const f=work.pop();
    if(f.kind==="build"){
      let out;
      if(f.tag==="proj")out=k.make("proj",f.name,f.index,vals.pop());
      else{
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--)xs[i]=vals.pop();
        out=k.make(f.tag,...xs);
      }
      stats.deepNormalBuilds++;
      f.slot.set(out);vals.push(out);continue;
    }
    stats.deepNormalVisits++;
    const requested=f.e,ctx=f.ctx,key=deepNormCtxKey(k,ctx,requested),slot=deepNormSlot(k,requested,key);
    if(slot?.has()){stats.deepNormalHits++;vals.push(slot.get());continue;}
    k.tick();
    const e=scopedWhnf(k,requested,ctx);
    if(e!==requested){
      const reducedSlot=deepNormSlot(k,e,key);
      if(reducedSlot?.has()){
        const out=reducedSlot.get();
        stats.deepNormalReducedHits++;
        slot?.set(out);vals.push(out);continue;
      }
    }
    if(["sort","var","const","nat","strlit"].includes(e[0])){
      slot?.set(e);
      if(e!==requested)deepNormSlot(k,e,key)?.set(e);
      vals.push(e);continue;
    }
    if(e[0]==="proj"){
      work.push({kind:"build",tag:"proj",name:e[1],index:e[2],slot});
      work.push({kind:"visit",e:e[3],ctx});continue;
    }
    work.push({kind:"build",tag:e[0],n:e.length-1,slot});
    if(e[0]==="pi" || e[0]==="lam"){
      // Domain is interpreted in the current context; body is interpreted under
      // one fresh ordinary binder. This is the critical de-Bruijn distinction.
      work.push({kind:"visit",e:e[2],ctx:[...ctx,e[1]]});
      work.push({kind:"visit",e:e[1],ctx});
      continue;
    }
    for(let i=e.length-1;i>=1;i--)work.push({kind:"visit",e:e[i],ctx});
  }
  return vals.pop();
}
function install(enabled){
  proto.run=retainedRun;proto.equal=retainedEqual;proto.whnf=retainedWhnf;proto.normal=retainedNormal;proto.substitute=retainedSubstitute;
  if(!enabled)return;
  proto.run=function(...args){
    this.__pairEq=new WeakMap();this.__pairIds=new WeakMap();this.__pairNextId=1;
    this.__pairWhnfWeak=new WeakMap();this.__pairWhnfRoot=new Map();this.__pairWhnfCache=new WeakMap();
    this.__deepNormIds=new WeakMap();this.__deepNormNextId=1;this.__deepNormCache=new WeakMap();this.__freeNeed=new WeakMap();
    subReset();
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
  proto.substitute=function(root,arg,depth=0){
    const key=subRecord(this,root,arg,depth);
    const out=retainedSubstitute.call(this,root,arg,depth);
    subReturned(key,out);
    return out;
  };
  proto.normal=function(e){
    if(this.localDefs===true)return deepLocalNormal(this,e);
    return retainedNormal.call(this,e);
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

function evaluate(budget,enabled,rows){
  install(enabled);atlasReset();const restoreAtlas=atlasWrap();
  const before={...stats},results=[];let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  try{
    for(const row of rows){
      const r=K.checkExport(row.input,caps,budget);
      totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
      if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
      results.push({name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
        frontier_declaration:r.frontier_declaration??null});
    }
  }finally{restoreAtlas();}
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  return {budget,enabled,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results,tailAtlas:atlasSummary()};
}

const report=evaluate(2100000,true,focusRows);
install(false);
console.log("KERNEL_RG_SUBSTITUTE_STATES "+JSON.stringify({scopeMode,report,substitution:subSummary()}));
