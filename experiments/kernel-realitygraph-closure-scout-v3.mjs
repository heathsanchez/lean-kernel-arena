import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop,UNKNOWN} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
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

const proto=K.Kernel.prototype,retainedRun=proto.run,retainedEqual=proto.equal,retainedWhnf=proto.whnf,retainedNormal=proto.normal;
const stats={eqHits:0,eqStores:0,earlyPi:0,frontiers:0,projectionEligible:0,projectionSuccess:0,argChecks:0,whnfQueries:0,whnfHits:0,whnfStores:0,whnfCanonNodes:0,whnfLocalBypass:0,deepNormalCalls:0,deepNormalVisits:0,deepNormalHits:0,deepNormalReducedHits:0,deepNormalStores:0,deepNormalBuilds:0,deepNormalCtxKeys:0,deepNormalEntries:0,supportQueries:0,supportZero:0,supportMax:0,supportCtxSaved:0};

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

const leanName=(...parts)=>parts.reduce((p,x)=>JSON.stringify([p,"str",x]),"[]");
const N_EQ=leanName("Eq"),N_BOOL=leanName("Bool"),N_TRUE=leanName("Bool","true"),N_FALSE=leanName("Bool","false");
const N_NAT_ZERO=leanName("Nat","zero"),N_NAT_SUCC=leanName("Nat","succ");
let closureScout={attempted:0,completed:0,failed:0,last:null,stuckRecs:[]};

function termShape(e){
  if(!Array.isArray(e))return {tag:typeof e,preview:String(e)};
  const raw=JSON.stringify(e);
  return {tag:e[0],bytes:raw.length,preview:raw.slice(0,700)};
}
function pureSame(a,b){
  if(a===b)return true;
  if(!Array.isArray(a)||!Array.isArray(b)||a.length!==b.length)return false;
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
const C=(term,env=[])=>({term,env});
function closureSame(a,b){
  return (a.term===b.term&&a.env===b.env) ||
    (a.env.length===0&&b.env.length===0&&pureSame(a.term,b.term));
}
function closureEvalSpine(k,start,initialArgs=[],limit=2000000){
  let cl=start,args=initialArgs.slice(),ops=0,maxArgs=args.length,maxEnv=cl.env.length,recReductions=0,beta=0,defs=0,vars=0;
  const bump=()=>{if(++ops>limit)throw new Error("closure-scout-budget");};
  for(;;){
    bump();
    const t=cl.term,e=cl.env;
    maxArgs=Math.max(maxArgs,args.length);maxEnv=Math.max(maxEnv,e.length);
    if(!Array.isArray(t))throw new Error("closure-nonterm");

    if(t[0]==="app"){
      args.unshift(C(t[2],e));
      cl=C(t[1],e);
      continue;
    }
    if(t[0]==="var"){
      if(t[1]>=e.length)throw new Error("closure-free-var:"+t[1]+"/"+e.length);
      vars++;cl=e[t[1]];continue;
    }
    if(t[0]==="let"){
      cl=C(t[3],[C(t[2],e),...e]);
      continue;
    }
    if(t[0]==="lam"&&args.length){
      beta++;cl=C(t[2],[args.shift(),...e]);continue;
    }
    if(t[0]==="nat"){
      if(t[1]===0){cl=C(["const",N_NAT_ZERO],[]);continue;}
      args.unshift(C(["nat",t[1]-1],[]));
      cl=C(["const",N_NAT_SUCC],[]);
      continue;
    }
    if(t[0]==="proj"){
      const obj=closureEvalSpine(k,C(t[3],e),[],limit-ops);
      ops+=obj.stats.ops;maxArgs=Math.max(maxArgs,obj.stats.maxArgs);maxEnv=Math.max(maxEnv,obj.stats.maxEnv);
      const h=obj.head.term,ind=k.env.get(t[1]);
      if(ind?.kind!=="inductive"||ind.ctors?.length!==1||h?.[0]!=="const"||h[1]!==ind.ctors[0])
        throw new Error("closure-proj-stuck");
      const pos=ind.numParams+t[2];
      if(pos>=obj.args.length)throw new Error("closure-proj-range");
      cl=obj.args[pos];continue;
    }
    if(t[0]==="const"){
      const d=k.env.get(t[1]);
      if(!d)throw new Error("closure-undeclared:"+t[1]);
      if(d.kind==="def"){
        defs++;cl=C(d.value,[]);continue;
      }
      if(d.kind==="rec"){
        const total=d.numParams+1+d.numMinors+d.numIndices+1;
        if(args.length>=total){
          const major=closureEvalSpine(k,args[total-1],[],limit-ops);
          ops+=major.stats.ops;maxArgs=Math.max(maxArgs,major.stats.maxArgs);maxEnv=Math.max(maxEnv,major.stats.maxEnv);
          const mh=major.head.term,md=mh?.[0]==="const"?k.env.get(mh[1]):null;
          if(md?.kind==="ctor"&&md.induct===d.induct&&major.args.length===md.numParams+md.numFields){
            let paramsMatch=true;
            for(let i=0;i<d.numParams;i++)if(!closureSame(major.args[i],args[i])){paramsMatch=false;break;}
            if(paramsMatch){
              const rule=d.rules.find(rr=>rr.ctor===md.name);
              if(rule){
                recReductions++;
                const prefix=args.slice(0,d.numParams+1+d.numMinors);
                const fields=major.args.slice(md.numParams);
                const extras=args.slice(total);
                args=prefix.concat(fields,extras);
                cl=C(rule.rhs,[]);
                continue;
              }
            }
          }
          if(closureScout.stuckRecs.length<12){
            closureScout.stuckRecs.push({
              rec:t[1],induct:d.induct,numParams:d.numParams,numMinors:d.numMinors,numIndices:d.numIndices,total,argsLength:args.length,
              majorHead:major.head.term?.[0]==="const"?major.head.term[1]:major.head.term?.[0],
              majorHeadKind:md?.kind??null,majorInduct:md?.induct??null,
              majorArgs:major.args.length,ctorParams:md?.numParams??null,ctorFields:md?.numFields??null,
              paramSame:Array.from({length:d.numParams},(_,i)=>closureSame(major.args[i],args[i])),
              recParamTerms:Array.from({length:d.numParams},(_,i)=>({a:termShape(major.args[i]?.term),b:termShape(args[i]?.term),
                aEnv:major.args[i]?.env?.length??null,bEnv:args[i]?.env?.length??null}))
            });
          }
        }
      }
    }
    return {head:cl,args,stats:{ops,maxArgs,maxEnv,recReductions,beta,defs,vars}};
  }
}
function evalClosedBool(k,term){
  const r=closureEvalSpine(k,C(term,[]));
  const h=r.head.term;
  if(r.args.length===0&&h?.[0]==="const"&&(h[1]===N_TRUE||h[1]===N_FALSE))
    return {value:h[1]===N_TRUE,stats:r.stats,head:h[1]};
  return {value:null,stats:r.stats,head:Array.isArray(h)?h.slice(0,3):h,args:r.args.length};
}
function eqBoolArgs(e){
  const s=rawSpine(e);
  if(s.head?.[0]!=="const"||s.head[1]!==N_EQ||s.args.length!==3)return null;
  if(s.args[0]?.[0]!=="const"||s.args[0][1]!==N_BOOL)return null;
  return s.args.slice(1);
}
function isTrueTerm(e){return e?.[0]==="const"&&e[1]===N_TRUE;}
function maybeScout(k,a,b,ctx){
  if(closureScout.attempted||ctx.length!==0)return;
  const aa=eqBoolArgs(a),bb=eqBoolArgs(b);
  if(!aa||!bb)return;
  let complex=null;
  if(isTrueTerm(aa[0])&&isTrueTerm(aa[1]))complex=bb;
  else if(isTrueTerm(bb[0])&&isTrueTerm(bb[1]))complex=aa;
  if(!complex)return;
  closureScout.attempted++;
  const t0=Date.now();
  try{
    const left=evalClosedBool(k,complex[0]),right=evalClosedBool(k,complex[1]);
    closureScout.completed++;
    closureScout.last={left,right,elapsed_ms:Date.now()-t0,kernel_step_at_scout:k.steps};
  }catch(err){
    closureScout.failed++;
    closureScout.last={error:String(err?.message??err),elapsed_ms:Date.now()-t0,kernel_step_at_scout:k.steps};
  }
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
function freeSupport(k,e){
  stats.supportQueries++;
  if(!Array.isArray(e))return 0;
  k.__freeSupport??=new WeakMap();
  const old=k.__freeSupport.get(e);if(old!==undefined){if(old===0)stats.supportZero++;stats.supportMax=Math.max(stats.supportMax,old);return old;}
  const walk=(x,depth)=>{
    if(!Array.isArray(x))return -1;
    if(x[0]==="var")return x[1]>=depth?x[1]-depth:-1;
    if(x[0]==="sort"||x[0]==="const"||x[0]==="nat"||x[0]==="strlit")return -1;
    if(x[0]==="proj")return walk(x[3],depth);
    if(x[0]==="lam"||x[0]==="pi")return Math.max(walk(x[1],depth),walk(x[2],depth+1));
    if(x[0]==="let")return Math.max(walk(x[1],depth),walk(x[2],depth),walk(x[3],depth+1));
    let m=-1;for(let i=1;i<x.length;i++)m=Math.max(m,walk(x[i],depth));return m;
  };
  const n=walk(e,0)+1;
  k.__freeSupport.set(e,n);
  if(n===0)stats.supportZero++;stats.supportMax=Math.max(stats.supportMax,n);
  return n;
}
function supportCtx(k,e,ctx){
  const n=freeSupport(k,e);
  const keep=Math.min(n,ctx?.length??0);
  stats.supportCtxSaved+=(ctx?.length??0)-keep;
  return keep===0?[]:ctx.slice(ctx.length-keep);
}
function deepNormCtxKey(k,ctx){
  stats.deepNormalCtxKeys++;
  if(!ctx?.length)return "";
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
    const requested=f.e,ctx=f.ctx,key=deepNormCtxKey(k,supportCtx(k,requested,ctx)),slot=deepNormSlot(k,requested,key);
    if(slot?.has()){stats.deepNormalHits++;vals.push(slot.get());continue;}
    k.tick();
    const e=scopedWhnf(k,requested,ctx);
    if(e!==requested){
      const reducedKey=deepNormCtxKey(k,supportCtx(k,e,ctx)),reducedSlot=deepNormSlot(k,e,reducedKey);
      if(reducedSlot?.has()){
        const out=reducedSlot.get();
        stats.deepNormalReducedHits++;
        slot?.set(out);vals.push(out);continue;
      }
    }
    if(["sort","var","const","nat","strlit"].includes(e[0])){
      slot?.set(e);
      if(e!==requested){const reducedKey=deepNormCtxKey(k,supportCtx(k,e,ctx));deepNormSlot(k,e,reducedKey)?.set(e);}
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
  proto.run=retainedRun;proto.equal=retainedEqual;proto.whnf=retainedWhnf;proto.normal=retainedNormal;
  if(!enabled)return;
  proto.run=function(...args){
    this.__pairEq=new WeakMap();this.__pairIds=new WeakMap();this.__pairNextId=1;
    this.__pairWhnfWeak=new WeakMap();this.__pairWhnfRoot=new Map();this.__pairWhnfCache=new WeakMap();
    this.__deepNormIds=new WeakMap();this.__deepNormNextId=1;this.__deepNormCache=new WeakMap();this.__freeSupport=new WeakMap();
    closureScout={attempted:0,completed:0,failed:0,last:null,stuckRecs:[]};
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
  proto.normal=function(e){
    if(this.localDefs===true)return deepLocalNormal(this,e);
    return retainedNormal.call(this,e);
  };
  proto.equal=function(a,b,ctx=[]){
    if(Array.isArray(a)&&Array.isArray(b))maybeScout(this,a,b,ctx);
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

const result=evaluate(1500000,true,focusRows);
install(false);
console.log("KERNEL_RG_CLOSURE_SCOUT_V3 "+JSON.stringify({arena_sha256:sha,result,closureScout}));
