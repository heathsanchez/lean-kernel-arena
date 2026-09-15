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
const stats={eqHits:0,eqStores:0,earlyPi:0,frontiers:0,projectionEligible:0,projectionSuccess:0,argChecks:0,whnfQueries:0,whnfHits:0,whnfStores:0,whnfCanonNodes:0,whnfLocalBypass:0,betaQueries:0,betaEligible:0,betaSuccesses:0,betaBinders:0,betaSubstNodes:0,betaSubstHits:0,betaFallbacks:0};

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


function structuralWhnf(k,e){
  if(k.localDefs===true || !Array.isArray(e)){
    if(k.localDefs===true)stats.whnfLocalBypass++;
    return retainedWhnf.call(k,e);
  }
  stats.whnfQueries++;
  const r=whnfRep(k,e);
  if(k.__pairWhnfCache?.has(r)){stats.whnfHits++;return k.__pairWhnfCache.get(r);}
  const out=retainedWhnf.call(k,e);
  k.__pairWhnfCache.set(r,out);stats.whnfStores++;
  return out;
}
function rebuildBeta(k,h,args){
  let out=h;for(const a of args)out=k.make("app",out,a);return out;
}
function substManyBeta(k,body,args){
  const m=args.length,memo=new WeakMap();
  function go(e,depth){
    if(!Array.isArray(e))return e;
    let byDepth=memo.get(e);
    if(!byDepth){byDepth=new Map();memo.set(e,byDepth);}
    if(byDepth.has(depth)){stats.betaSubstHits++;return byDepth.get(depth);}
    stats.betaSubstNodes++;
    let out=e;
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit": out=e;break;
      case "var":{
        const i=e[1];
        if(i<depth)out=e;
        else{
          const j=i-depth;
          if(j<m)out=k.shift(args[m-1-j],depth);
          else out=k.make("var",i-m);
        }
        break;
      }
      case "pi":case "lam":{
        const a=go(e[1],depth),b=go(e[2],depth+1);
        out=(a===e[1]&&b===e[2])?e:k.make(e[0],a,b);break;
      }
      case "app":{
        const f=go(e[1],depth),a=go(e[2],depth);
        out=(f===e[1]&&a===e[2])?e:k.make("app",f,a);break;
      }
      case "proj":{
        const x=go(e[3],depth);
        out=x===e[3]?e:k.make("proj",e[1],e[2],x);break;
      }
      case "let":{
        const a=go(e[1],depth),v=go(e[2],depth),b=go(e[3],depth+1);
        out=(a===e[1]&&v===e[2]&&b===e[3])?e:k.make("let",a,v,b);break;
      }
      default:k.unknown("external-beta-syntax");
    }
    byDepth.set(depth,out);return out;
  }
  return go(body,0);
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
    if(this.localDefs===true || this.__pairExternalBetaDepth || !Array.isArray(e) || e[0]!=="app")
      return structuralWhnf(this,e);

    stats.betaQueries++;
    const sp=rawSpine(e);
    if(sp.args.length<2){stats.betaFallbacks++;return structuralWhnf(this,e);}

    // Probe only the flattened head. Misses are charged rather than rolled back,
    // so this separator cannot manufacture a speedup from speculative work.
    this.__pairExternalBetaDepth=1;
    try{
      const head=structuralWhnf(this,sp.head);
      let cur=head,m=0;
      while(m<sp.args.length && Array.isArray(cur) && cur[0]==="lam"){
        m++;cur=cur[2];
      }
      if(m<2){
        stats.betaFallbacks++;
        return structuralWhnf(this,e);
      }
      stats.betaEligible++;stats.betaBinders+=m;
      for(let i=0;i<m;i++){this.tick();this.need("application");this.need("reduction");}
      const out=substManyBeta(this,cur,sp.args.slice(0,m));
      const next=sp.args.length===m?out:rebuildBeta(this,out,sp.args.slice(m));
      const result=structuralWhnf(this,next);
      stats.betaSuccesses++;
      return result;
    }finally{
      this.__pairExternalBetaDepth=0;
    }
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
  const before={...stats},results=[];let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null});
  }
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  return {budget,enabled,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results};
}
const thresholds=[];
for(const budget of [1000000,1250000,1500000,2000000]){
  thresholds.push(evaluate(budget,true,focusRows));
}
install(false);
console.log("PAIR_BETA_WHNF_THRESHOLDS "+JSON.stringify(thresholds));

const at1m=thresholds[0];
if(at1m.wrong||!at1m.results.some(r=>r.status==="ACCEPT")){
  console.log("PAIR_BETA_WHNF_STOP "+JSON.stringify({reason:"not-closed-at-1m",thresholds}));
  process.exit(0);
}

const pyAll=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",pyAll],{input:data,maxBuffer:50000000,timeout:10000}));
const candidate=evaluate(1000000,true,rows),baseline=evaluate(1000000,false,rows);install(false);
if(candidate.wrong||baseline.wrong)throw new Error("wrong verdict");
let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});}
  if(b.status==="UNKNOWN"){
    if(c.status!=="UNKNOWN"&&c.status===rows[i].expected)resolved.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
    else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
  }
}
const report={arena_sha256:sha,budget:1000000,thresholds,
 baseline:{totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed},
 candidate:{totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,stats:candidate.stats,
 protectedChanged,resolved,regressions,remaining},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved.length>0,
 claim_boundary:"Composition of execution-only consequences: exact structural ordinary-kernel WHNF reuse, simultaneous external beta-spine substitution, early Pi congruence, exact successful equality memory, and positive recursor-projection recovery. LocalDef WHNF/beta remain excluded. The beta spine implements repeated beta reduction exactly; no typing, equality or reduction law is added."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/pair-beta-whnf.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("PAIR_BETA_WHNF "+JSON.stringify(report));
