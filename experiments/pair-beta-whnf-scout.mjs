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

const proto=K.Kernel.prototype,retainedRun=proto.run,retainedEqual=proto.equal,retainedWhnf=proto.whnf;
const stats={eqHits:0,eqStores:0,earlyPi:0,frontiers:0,projectionEligible:0,projectionSuccess:0,argChecks:0,whnfQueries:0,whnfHits:0,whnfStores:0,whnfCanonNodes:0,whnfLocalBypass:0,localWhnfQueries:0,localWhnfHits:0,localWhnfStores:0,natPrimitiveQueries:0,natAdd:0,natMul:0,natMod:0,headDecide:0,headForallFin:0,headBallLT:0,headDecidableOfIff:0,headEqFin:0,headMagmaOp:0,headCountermodelOp:0,betaQueries:0,betaEligible:0,betaSuccesses:0,betaBinders:0,betaSubstNodes:0,betaSubstHits:0,betaFallbacks:0};

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

function lname(...parts){
  let n="[]";
  for(const p of parts)n=JSON.stringify([n,"str",p]);
  return n;
}
const NAT_ZERO=lname("Nat","zero"),NAT_SUCC=lname("Nat","succ");
const NAT_ADD=lname("Nat","add"),NAT_MUL=lname("Nat","mul"),NAT_MOD=lname("Nat","mod");
const DECIDE=lname("Decidable","decide"),FORALL_FIN=lname("Nat","decidableForallFin"),BALL_LT=lname("Nat","decidableBallLT");
const DECIDABLE_OF_IFF=lname("decidable_of_iff"),EQ_FIN=lname("instDecidableEqFin"),MAGMA_OP=lname("Magma","op"),COUNTERMODEL_OP=lname("countermodel","op");
function countHead(e){
  if(!Array.isArray(e)||e[0]!=="app")return;
  const sp=rawSpine(e);if(sp.head?.[0]!=="const")return;
  switch(sp.head[1]){
    case DECIDE:stats.headDecide++;break;
    case FORALL_FIN:stats.headForallFin++;break;
    case BALL_LT:stats.headBallLT++;break;
    case DECIDABLE_OF_IFF:stats.headDecidableOfIff++;break;
    case EQ_FIN:stats.headEqFin++;break;
    case MAGMA_OP:stats.headMagmaOp++;break;
    case COUNTERMODEL_OP:stats.headCountermodelOp++;break;
  }
}

function closedNat(e,limit=1000000){
  if(!Array.isArray(e))return null;
  if(e[0]==="nat"&&Number.isSafeInteger(e[1])&&e[1]>=0)return e[1];
  if(e[0]==="const"&&e[1]===NAT_ZERO)return 0;
  let n=0,cur=e;
  while(Array.isArray(cur)&&cur[0]==="app"&&Array.isArray(cur[1])&&cur[1][0]==="const"&&cur[1][1]===NAT_SUCC){
    n++;if(n>limit)return null;cur=cur[2];
  }
  if(n){
    const tail=closedNat(cur,limit-n);
    return tail===null?null:n+tail;
  }
  return null;
}
function natWhnf(k,n){
  if(n===0)return ["const",NAT_ZERO];
  return k.make("app",["const",NAT_SUCC],k.make("nat",n-1));
}
function nativeNatPrimitive(k,e){
  if(!Array.isArray(e)||e[0]!=="app")return null;
  const sp=rawSpine(e);
  if(sp.head?.[0]!=="const"||sp.args.length!==2)return null;
  const h=sp.head[1];
  if(h!==NAT_ADD&&h!==NAT_MUL&&h!==NAT_MOD)return null;
  stats.natPrimitiveQueries++;
  const a=closedNat(sp.args[0]),b=closedNat(sp.args[1]);
  if(a===null||b===null)return null;
  let v;
  if(h===NAT_ADD){v=a+b;stats.natAdd++;}
  else if(h===NAT_MUL){v=a*b;stats.natMul++;}
  else {if(b===0)return null;v=a%b;stats.natMod++;}
  if(!Number.isSafeInteger(v)||v<0)return null;
  k.tick();k.need("reduction");
  return natWhnf(k,v);
}

const WHNF_END=Symbol("whnf-end");
function whnfEnsure(k){
  k.__pairWhnfWeak??=new WeakMap();k.__pairWhnfRoot??=new Map();k.__pairWhnfCache??=new WeakMap();k.__pairLocalWhnfCache??=new WeakMap();
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
  if(!Array.isArray(e))return retainedWhnf.call(k,e);
  const r=whnfRep(k,e);
  if(k.localDefs===true){
    stats.localWhnfQueries++;
    const key=ctxKey(k,k._activeCtx??[]);
    let byCtx=k.__pairLocalWhnfCache?.get(r);
    if(!byCtx){byCtx=new Map();k.__pairLocalWhnfCache.set(r,byCtx);}
    if(byCtx.has(key)){stats.localWhnfHits++;return byCtx.get(key);}
    const out=retainedWhnf.call(k,e);
    byCtx.set(key,out);stats.localWhnfStores++;
    return out;
  }
  stats.whnfQueries++;
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
    this.__pairWhnfWeak=new WeakMap();this.__pairWhnfRoot=new Map();this.__pairWhnfCache=new WeakMap();this.__pairLocalWhnfCache=new WeakMap();
    return retainedRun.apply(this,args);
  };
  proto.whnf=function(e){
    countHead(e);
    if(Array.isArray(e)&&e[0]==="app"){
      const nat=nativeNatPrimitive(this,e);
      if(nat!==null)return nat;
    }
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
for(const budget of [1000000]){
  thresholds.push(evaluate(budget,true,focusRows));
}
install(false);
console.log("PAIR_BETA_WHNF_SCOUT_THRESHOLDS "+JSON.stringify(thresholds));

console.log("PAIR_BETA_WHNF_SCOUT "+JSON.stringify(thresholds));
process.exit(0);
