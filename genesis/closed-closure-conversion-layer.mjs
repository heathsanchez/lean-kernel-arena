import {Kernel,Stop} from "./kernel-base.mjs";

// Closed monomorphic closure conversion separator.
// It proves equality only by retained definitional reductions and congruence,
// while substitutions are represented as environments instead of materialized
// syntax. Anything outside the deliberately small envelope aborts and replays
// the retained converter from the exact semantic snapshot.
const p=Kernel.prototype,equal0=p.equal;
const ABORT=Symbol("closure-conversion-abort");
const EMPTY=Object.freeze([]);

function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return{h,args};
}
function headKind(k,e){
  const s=rawSpine(e),h=s.h;
  return Array.isArray(h)&&h[0]==="const"?(k.env?.get(h[1])?.kind??null):null;
}
function target(k,a,b,ctx){
  if(ctx.length!==0||!Array.isArray(a)||!Array.isArray(b))return false;
  const x=headKind(k,a),y=headKind(k,b),ok=new Set(["def","rec","ctor"]);
  return ok.has(x)||ok.has(y);
}
function machine(k){
  const termClosures=new WeakMap(),envCons=new WeakMap(),whnfCache=new WeakMap();
  let closureNext=1;
  const stats={ops:0,beta:0,defs:0,recs:0,vars:0,apps:0,whnfHits:0,whnfStores:0,
    ctorPairs:0,rigidPairs:0,maxEnv:0,maxArgs:0};

  function C(term,env=EMPTY){
    if(!env.length)env=EMPTY;
    if(!Array.isArray(term))return {term,env,__id:closureNext++};
    let by=termClosures.get(term);
    if(!(by instanceof WeakMap)){by=new WeakMap();termClosures.set(term,by);}
    let c=by.get(env);if(c!==undefined)return c;
    c={term,env,__id:closureNext++};by.set(env,c);return c;
  }
  function cons(item,parent){
    let by=envCons.get(parent);
    if(!(by instanceof WeakMap)){by=new WeakMap();envCons.set(parent,by);}
    let e=by.get(item);if(e!==undefined)return e;
    e=Object.freeze([item,...parent]);by.set(item,e);return e;
  }
  function bump(){
    k.tick();stats.ops++;
    if(stats.ops>900000)throw ABORT;
  }
  function sameLevels(a,b){return JSON.stringify(a??[])===JSON.stringify(b??[]);}

  function whnf(start,depth=0){
    if(depth>6000)throw ABORT;
    const old=whnfCache.get(start);
    if(old!==undefined){stats.whnfHits++;return old;}

    let cl=start,args=[];
    for(let guard=0;guard<200000;guard++){
      bump();
      stats.maxEnv=Math.max(stats.maxEnv,cl.env.length);
      stats.maxArgs=Math.max(stats.maxArgs,args.length);
      const t=cl.term,env=cl.env;
      if(!Array.isArray(t))throw ABORT;

      if(t[0]==="app"){
        k.need("application");stats.apps++;
        args.unshift(C(t[2],env));cl=C(t[1],env);continue;
      }
      if(t[0]==="var"){
        if(t[1]>=env.length)throw ABORT;
        stats.vars++;cl=env[t[1]];continue;
      }
      if(t[0]==="let"){
        k.need("reduction");
        cl=C(t[3],cons(C(t[2],env),env));continue;
      }
      if(t[0]==="lam"&&args.length){
        k.need("reduction");stats.beta++;
        cl=C(t[2],cons(args.shift(),env));continue;
      }
      if(t[0]==="proj")throw ABORT;
      if(t[0]==="nat"||t[0]==="strlit"||t[0]==="sort"||t[0]==="pi"||t[0]==="lam"){
        const out={head:cl,args:Object.freeze(args.slice())};
        whnfCache.set(start,out);stats.whnfStores++;return out;
      }
      if(t[0]!=="const")throw ABORT;

      k.need("declarations");
      const d=k.env.get(t[1]);if(!d)k.reject("undeclared-constant");
      if(d.kind==="def"){
        k.need("reduction");stats.defs++;
        const body=k.instantiateDeclaration(t,d.value);
        cl=C(body,EMPTY);continue;
      }
      if(d.kind==="rec"&&args.length>=d.numParams+1+d.numMinors+d.numIndices+1){
        // Deliberate separator boundary: the shared-DAG family is non-indexed
        // and parameter-free. Anything broader is left to retained semantics.
        if(d.numParams!==0||d.numIndices!==0)throw ABORT;
        const total=1+d.numMinors+1,major=whnf(args[total-1],depth+1);
        const mh=major.head.term,md=Array.isArray(mh)&&mh[0]==="const"?k.env.get(mh[1]):null;
        if(md?.kind==="ctor"&&md.induct===d.induct&&major.args.length===md.numFields){
          const rule=d.rules.find(r=>r.ctor===md.name);
          if(!rule)throw ABORT;
          k.need("inductive-reduction");k.need("reduction");stats.recs++;
          const rhs=k.instantiateDeclaration(t,rule.rhs);
          const prefix=args.slice(0,1+d.numMinors),extras=args.slice(total);
          args=prefix.concat(major.args,extras);
          cl=C(rhs,EMPTY);continue;
        }
      }

      const out={head:cl,args:Object.freeze(args.slice())};
      whnfCache.set(start,out);stats.whnfStores++;return out;
    }
    throw ABORT;
  }

  function prove(a,b){
    const work=[[C(a,EMPTY),C(b,EMPTY)]];
    for(let guard=0;work.length&&guard<200000;guard++){
      const [ca,cb]=work.pop();
      if(ca===cb)continue;
      const x=whnf(ca),y=whnf(cb);
      if(x.head===y.head&&x.args.length===y.args.length&&x.args.every((q,i)=>q===y.args[i]))continue;

      const a0=x.head.term,b0=y.head.term;
      if(!Array.isArray(a0)||!Array.isArray(b0)||a0[0]!==b0[0])throw ABORT;

      if(a0[0]==="const"){
        if(a0[1]!==b0[1]||!sameLevels(a0[2],b0[2])||x.args.length!==y.args.length)throw ABORT;
        const d=k.env.get(a0[1]);
        if(d?.kind==="ctor")stats.ctorPairs++;else stats.rigidPairs++;
        for(let i=x.args.length-1;i>=0;i--)work.push([x.args[i],y.args[i]]);
        continue;
      }
      if(a0[0]==="nat"||a0[0]==="strlit"){
        if(a0[1]!==b0[1]||x.args.length||y.args.length)throw ABORT;
        stats.rigidPairs++;continue;
      }
      if(a0[0]==="sort"){
        if(JSON.stringify(a0[1])!==JSON.stringify(b0[1])||x.args.length||y.args.length)throw ABORT;
        stats.rigidPairs++;continue;
      }
      throw ABORT;
    }
    if(work.length||stats.ctorPairs===0)throw ABORT;
    return stats;
  }
  return {prove};
}

p.equal=function(a,b,ctx=[]){
  if(this.localDefs===true||!target(this,a,b,ctx))return equal0.call(this,a,b,ctx);
  this.__closedClosureStats??={attempts:0,successes:0,aborts:0,ops:0,ctorPairs:0,whnfHits:0,recs:0,beta:0};
  this.__closedClosureStats.attempts++;
  const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
  try{
    const st=machine(this).prove(a,b);
    this.__closedClosureStats.successes++;
    for(const q of ["ops","ctorPairs","whnfHits","recs","beta"])this.__closedClosureStats[q]+=st[q]??0;
    return;
  }catch(err){
    if(err!==ABORT&&!(err instanceof Stop)&&!(err instanceof RangeError))throw err;
    this.__closedClosureStats.aborts++;
    this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    return equal0.call(this,a,b,ctx);
  }
};
