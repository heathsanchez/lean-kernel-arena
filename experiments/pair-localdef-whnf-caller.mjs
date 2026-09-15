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

const proto=K.Kernel.prototype,retainedRun=proto.run,retainedEqual=proto.equal,retainedWhnf=proto.whnf,retainedInfer=proto.infer;
const stats={eqHits:0,eqStores:0,earlyPi:0,frontiers:0,projectionEligible:0,projectionSuccess:0,argChecks:0,whnfQueries:0,whnfHits:0,whnfStores:0,whnfCanonNodes:0,whnfLocalBypass:0,closedInferQueries:0,closedInferEligible:0,closedInferHits:0,closedInferStores:0,closedChecks:0};

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


function closedRoot(k,e){
  if(!Array.isArray(e))return false;
  k.__closedInferClosed??=new WeakMap();
  const old=k.__closedInferClosed.get(e);
  if(old!==undefined)return old;

  const memo=new WeakMap();
  function walk(x,depth){
    if(!Array.isArray(x))return true;
    let byDepth=memo.get(x);
    if(!byDepth){byDepth=new Map();memo.set(x,byDepth);}
    if(byDepth.has(depth))return byDepth.get(depth);
    stats.closedChecks++;
    let ok=true;
    switch(x[0]){
      case "sort":case "const":case "nat":case "strlit": ok=true;break;
      case "var": ok=x[1]<depth;break;
      case "pi":case "lam": ok=walk(x[1],depth)&&walk(x[2],depth+1);break;
      case "app": ok=walk(x[1],depth)&&walk(x[2],depth);break;
      case "proj": ok=walk(x[3],depth);break;
      case "let": ok=walk(x[1],depth)&&walk(x[2],depth)&&walk(x[3],depth+1);break;
      default: ok=false;
    }
    byDepth.set(depth,ok);return ok;
  }
  const out=walk(e,0);
  k.__closedInferClosed.set(e,out);
  return out;
}

const whnfTail={ids:new WeakMap(),next:1,records:new Map(),calls:0,ctxDepths:new Map(),stepBuckets:new Map()};
const callerDiag={stack:[],counts:new Map()};
function rawShape(e){
  if(!Array.isArray(e))return {tag:typeof e,spine:0,head:null};
  let h=e,n=0;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  let head=h?.[0]??typeof h;
  if(Array.isArray(h)&&h[0]==="const")head="const:"+h[1];
  else if(Array.isArray(h)&&h[0]==="var")head="var:"+h[1];
  else if(Array.isArray(h)&&h[0]==="proj")head="proj:"+h[1]+":"+h[2];
  return {tag:e[0],spine:n,head};
}
function tailRecord(k,e){
  if(k.localDefs!==true || k.steps<2000000 || !Array.isArray(e)) return;
  whnfTail.calls++;
  let id=whnfTail.ids.get(e);
  if(id===undefined){
    id=whnfTail.next++;whnfTail.ids.set(e,id);
    whnfTail.records.set(id,{id,count:0,returns:0,...rawShape(e),firstStep:k.steps,lastStep:k.steps,
      firstDeclaration:k.currentDeclaration??null,lastDeclaration:k.currentDeclaration??null,
      outputShapes:new Map()});
  }
  const r=whnfTail.records.get(id);r.count++;r.lastStep=k.steps;r.lastDeclaration=k.currentDeclaration??null;
  const caller=callerDiag.stack.length?callerDiag.stack.join(">"):"<none>";
  callerDiag.counts.set(caller,(callerDiag.counts.get(caller)??0)+1);
  const d=k._activeCtx?.length??0;whnfTail.ctxDepths.set(d,(whnfTail.ctxDepths.get(d)??0)+1);
  const b=Math.floor(k.steps/500000)*500000;
  whnfTail.stepBuckets.set(b,(whnfTail.stepBuckets.get(b)??0)+1);
  return id;
}
function tailReturn(id,out){
  if(id===undefined)return;
  const r=whnfTail.records.get(id);if(!r)return;
  r.returns++;
  const sh=rawShape(out);const key=sh.tag+"|"+sh.spine+"|"+sh.head;
  r.outputShapes.set(key,(r.outputShapes.get(key)??0)+1);
}
function tailSummary(){
  const top=[...whnfTail.records.values()].sort((a,b)=>b.count-a.count).slice(0,50)
    .map(r=>({...r,outputShapes:[...r.outputShapes.entries()].map(([shape,count])=>({shape,count}))}));
  const byShape=new Map();
  for(const r of whnfTail.records.values()){
    const key=r.tag+"|"+r.spine+"|"+r.head;
    const x=byShape.get(key)??{tag:r.tag,spine:r.spine,head:r.head,calls:0,unique:0};
    x.calls+=r.count;x.unique++;byShape.set(key,x);
  }
  return {
    calls:whnfTail.calls,unique:whnfTail.records.size,
    topExact:top,
    topShapes:[...byShape.values()].sort((a,b)=>b.calls-a.calls).slice(0,40),
    ctxDepths:[...whnfTail.ctxDepths.entries()].sort((a,b)=>b[1]-a[1]).slice(0,30),
    stepBuckets:[...whnfTail.stepBuckets.entries()].sort((a,b)=>a[0]-b[0])
  };
}

function wrapCallers(){
  const names=["normal","equal","proofType","sortOf","infer","inferProjection","structureEtaMatches","isUnitLikeType"];
  const old=new Map();
  for(const name of names){
    const fn=proto[name];if(typeof fn!=="function")continue;
    old.set(name,fn);
    proto[name]=function(...args){
      callerDiag.stack.push(name);
      try{return fn.apply(this,args);}
      finally{callerDiag.stack.pop();}
    };
  }
  return ()=>{for(const [name,fn] of old)proto[name]=fn;};
}
function callerSummary(){
  return [...callerDiag.counts.entries()].sort((a,b)=>b[1]-a[1]).slice(0,40)
    .map(([caller,count])=>({caller,count}));
}
function install(enabled){
  proto.run=retainedRun;proto.equal=retainedEqual;proto.whnf=retainedWhnf;proto.infer=retainedInfer;
  if(!enabled)return;
  proto.run=function(...args){
    this.__pairEq=new WeakMap();this.__pairIds=new WeakMap();this.__pairNextId=1;
    this.__pairWhnfWeak=new WeakMap();this.__pairWhnfRoot=new Map();this.__pairWhnfCache=new WeakMap();
    this.__closedInferCache=new WeakMap();this.__closedInferClosed=new WeakMap();
    whnfTail.ids=new WeakMap();whnfTail.next=1;whnfTail.records=new Map();whnfTail.calls=0;whnfTail.ctxDepths=new Map();whnfTail.stepBuckets=new Map();
    return retainedRun.apply(this,args);
  };
  proto.whnf=function(e){
    if(this.localDefs===true || !Array.isArray(e)){
      let tid;
      if(this.localDefs===true){stats.whnfLocalBypass++;tid=tailRecord(this,e);}
      const out=retainedWhnf.call(this,e);
      if(this.localDefs===true)tailReturn(tid,out);
      return out;
    }
    stats.whnfQueries++;
    const r=whnfRep(this,e);
    if(this.__pairWhnfCache?.has(r)){stats.whnfHits++;return this.__pairWhnfCache.get(r);}
    const out=retainedWhnf.call(this,e);
    this.__pairWhnfCache.set(r,out);stats.whnfStores++;
    return out;
  };
  proto.infer=function(e,ctx=[]){
    if(!Array.isArray(e))return retainedInfer.call(this,e,ctx);
    stats.closedInferQueries++;
    if(!closedRoot(this,e))return retainedInfer.call(this,e,ctx);
    stats.closedInferEligible++;
    this.__closedInferCache??=new WeakMap();
    if(this.__closedInferCache.has(e)){stats.closedInferHits++;return this.__closedInferCache.get(e);}
    const out=retainedInfer.call(this,e,ctx);
    this.__closedInferCache.set(e,out);stats.closedInferStores++;
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

function evaluate(budget,enabled,rows){
  install(enabled);
  callerDiag.stack=[];callerDiag.counts=new Map();
  const restoreCallers=enabled?wrapCallers():()=>{};
  const before={...stats},results=[];let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null});
  }
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  const callers=callerSummary();restoreCallers();
  return {budget,enabled,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results,whnfTail:tailSummary(),callers};
}
const thresholds=[];
for(const budget of [2200000]){
  thresholds.push(evaluate(budget,true,focusRows));
}
install(false);
console.log("PAIR_LOCALDEF_WHNF_CALLER_THRESHOLDS "+JSON.stringify(thresholds));

console.log("PAIR_LOCALDEF_WHNF_CALLER "+JSON.stringify(thresholds));
process.exit(0);
