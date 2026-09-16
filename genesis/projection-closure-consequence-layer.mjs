import {Kernel,Stop} from "./kernel-base.mjs";

// Experimental exact consequence: close projection-headed conversion through a
// compact environment machine instead of materializing giant beta substitutions.
// No declaration name is special-cased.  The machine uses only ordinary Lean
// definitional rules: beta/let, transparent definitions, non-indexed recursor
// iota, Nat-literal constructors, and projection from the matching constructor.
// It may prove a comparison only if at least one projection actually reduces.
// Any unsupported shape rolls back completely to the retained converter.
const p=Kernel.prototype,equal0=p.equal,run0=p.run;
const ABORT=Symbol("projection-closure-abort");
const EMPTY=Object.freeze([]);
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
const NAT_ZERO=N("Nat","zero"),NAT_SUCC=N("Nat","succ");

function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return{h,args};
}
function projectionHeaded(e){return rawSpine(e).h?.[0]==="proj";}
function target(a,b,ctx){return ctx.length===0&&(projectionHeaded(a)||projectionHeaded(b));}

function machine(k){
  const termClosures=new WeakMap(),envCons=new WeakMap(),whnfCache=new WeakMap(),eqSuccess=new WeakMap();
  let nextId=1,attemptOps=0;
  const stats={ops:0,beta:0,lets:0,defs:0,recs:0,projs:0,vars:0,apps:0,whnfHits:0,whnfStores:0,eqHits:0,eqStores:0,lastAbort:null};

  function bump(){
    k.tick();stats.ops++;attemptOps++;
    if(attemptOps>450000){stats.lastAbort="op-cap";throw ABORT;}
  }
  function C(term,env=EMPTY){
    if(!Array.isArray(term))return {term,env,__id:nextId++};
    let by=termClosures.get(term);
    if(!(by instanceof WeakMap)){by=new WeakMap();termClosures.set(term,by);}
    let c=by.get(env);if(c!==undefined)return c;
    c={term,env,__id:nextId++};by.set(env,c);return c;
  }
  function cons(item,parent){
    let by=envCons.get(parent);
    if(!(by instanceof WeakMap)){by=new WeakMap();envCons.set(parent,by);}
    let e=by.get(item);if(e!==undefined)return e;
    e=Object.freeze([item,...parent]);by.set(item,e);return e;
  }
  function deref(start){
    let cl=start;
    for(let guard=0;guard<20000;guard++){
      const t=cl.term;
      if(!Array.isArray(t)||t[0]!=="var")return cl;
      if(t[1]>=cl.env.length){stats.lastAbort="free-var";throw ABORT;}
      bump();stats.vars++;cl=cl.env[t[1]];
    }
    stats.lastAbort="var-loop";throw ABORT;
  }
  function finish(start,head,args){
    const out={head,args:Object.freeze(args.slice())};
    whnfCache.set(start,out);stats.whnfStores++;return out;
  }
  function natValue(t){
    if(!Array.isArray(t)||t[0]!=="nat")return null;
    try{return BigInt(t[1]);}catch{return null;}
  }

  function whnf(start,depth=0){
    if(depth>8000){stats.lastAbort="depth";throw ABORT;}
    const old=whnfCache.get(start);if(old!==undefined){stats.whnfHits++;return old;}
    let cl=start,args=[];
    for(let guard=0;guard<300000;guard++){
      cl=deref(cl);
      const t=cl.term,env=cl.env;
      if(!Array.isArray(t)){stats.lastAbort="non-term";throw ABORT;}
      if(t[0]==="app"){
        bump();stats.apps++;
        args.unshift(C(t[2],env));cl=C(t[1],env);continue;
      }
      bump();
      if(t[0]==="let"){
        k.need("reduction");stats.lets++;
        cl=C(t[3],cons(C(t[2],env),env));continue;
      }
      if(t[0]==="lam"&&args.length){
        k.need("reduction");stats.beta++;
        cl=C(t[2],cons(args.shift(),env));continue;
      }
      if(t[0]==="proj"){
        k.need("projections");
        const ind=k.env?.get(t[1]);
        if(ind?.kind!=="inductive"||!Array.isArray(ind.ctors)||ind.ctors.length!==1){stats.lastAbort="projection-inductive";throw ABORT;}
        const obj=whnf(C(t[3],env),depth+1),ht=obj.head.term;
        const cd=Array.isArray(ht)&&ht[0]==="const"?k.env?.get(ht[1]):null;
        if(cd?.kind!=="ctor"||cd.induct!==ind.name||cd.name!==ind.ctors[0]){stats.lastAbort="projection-major";throw ABORT;}
        if(!Number.isSafeInteger(t[2])||t[2]<0||t[2]>=cd.numFields){stats.lastAbort="projection-index";throw ABORT;}
        const pos=ind.numParams+t[2];
        if(pos>=obj.args.length){stats.lastAbort="projection-arity";throw ABORT;}
        k.need("reduction");stats.projs++;
        cl=obj.args[pos];continue;
      }
      if(t[0]==="nat"){
        k.need("nat-literals");
        const n=natValue(t);if(n===null||n<0n){stats.lastAbort="nat";throw ABORT;}
        if(n===0n)return finish(start,C(["const",NAT_ZERO],EMPTY),args);
        const pred=["nat",(n-1n)<=BigInt(Number.MAX_SAFE_INTEGER)?Number(n-1n):(n-1n).toString()];
        return finish(start,C(["const",NAT_SUCC],EMPTY),[C(pred,EMPTY),...args]);
      }
      if(t[0]==="strlit"||t[0]==="sort"||t[0]==="pi"||t[0]==="lam")return finish(start,cl,args);
      if(t[0]!=="const"){stats.lastAbort="syntax:"+t[0];throw ABORT;}

      k.need("declarations");
      const d=k.env?.get(t[1]);if(!d){stats.lastAbort="undeclared";throw ABORT;}
      if(d.kind==="def"){
        k.need("reduction");stats.defs++;
        cl=C(k.instantiateDeclaration(t,d.value),EMPTY);continue;
      }
      if(d.kind==="rec"&&args.length>=d.numParams+1+d.numMinors+d.numIndices+1){
        if(d.numParams!==0||d.numIndices!==0){stats.lastAbort="param-or-indexed-rec";throw ABORT;}
        const total=1+d.numMinors+1,major=whnf(args[total-1],depth+1),mh=major.head.term;
        const md=Array.isArray(mh)&&mh[0]==="const"?k.env?.get(mh[1]):null;
        if(md?.kind!=="ctor"||md.induct!==d.induct||major.args.length!==md.numFields){stats.lastAbort="rec-major";throw ABORT;}
        const rule=d.rules?.find(r=>r.ctor===md.name);if(!rule){stats.lastAbort="rec-rule";throw ABORT;}
        k.need("inductive-reduction");k.need("reduction");stats.recs++;
        const rhs=k.instantiateDeclaration(t,rule.rhs),prefix=args.slice(0,1+d.numMinors),extras=args.slice(total);
        args=prefix.concat(major.args,extras);cl=C(rhs,EMPTY);continue;
      }
      return finish(start,cl,args);
    }
    stats.lastAbort="whnf-loop";throw ABORT;
  }

  function hasEq(a,b){return eqSuccess.get(a)?.has(b)===true;}
  function storeEq(a,b){
    let s=eqSuccess.get(a);if(!s){s=new WeakSet();eqSuccess.set(a,s);}s.add(b);
    let t=eqSuccess.get(b);if(!t){t=new WeakSet();eqSuccess.set(b,t);}t.add(a);stats.eqStores++;
  }
  function prove(a,b){
    attemptOps=0;stats.lastAbort=null;
    const ca=C(a,EMPTY),cb=C(b,EMPTY);if(hasEq(ca,cb)){stats.eqHits++;return stats;}
    const projsBefore=stats.projs,work=[[ca,cb]];
    for(let guard=0;work.length&&guard<300000;guard++){
      const [u,v]=work.pop();if(u===v)continue;
      const x=whnf(u),y=whnf(v);
      if(x.head===y.head&&x.args.length===y.args.length&&x.args.every((q,i)=>q===y.args[i]))continue;
      const a0=x.head.term,b0=y.head.term;
      if(!Array.isArray(a0)||!Array.isArray(b0)||a0[0]!==b0[0]){stats.lastAbort="head-tag";throw ABORT;}
      if(a0[0]==="const"){
        if(a0[1]!==b0[1]||JSON.stringify(a0[2]??[])!==JSON.stringify(b0[2]??[])||x.args.length!==y.args.length){stats.lastAbort="const-mismatch";throw ABORT;}
        for(let i=x.args.length-1;i>=0;i--)work.push([x.args[i],y.args[i]]);continue;
      }
      if(a0[0]==="strlit"){
        if(a0[1]!==b0[1]||x.args.length||y.args.length){stats.lastAbort="literal-mismatch";throw ABORT;}continue;
      }
      if(a0[0]==="sort"){
        if(JSON.stringify(a0[1])!==JSON.stringify(b0[1])||x.args.length||y.args.length){stats.lastAbort="sort-mismatch";throw ABORT;}continue;
      }
      stats.lastAbort="unsupported-head:"+a0[0];throw ABORT;
    }
    if(work.length||stats.projs===projsBefore){stats.lastAbort=work.length?"work-left":"no-projection";throw ABORT;}
    storeEq(ca,cb);return stats;
  }
  return {prove,stats};
}

p.run=function(...args){
  this.__projectionClosureMachine=null;
  this.__projectionClosure={attempts:0,successes:0,aborts:0,ops:0,projs:0,recs:0,beta:0,lastAbort:null};
  return run0.apply(this,args);
};

p.equal=function(a,b,ctx=[]){
  if(this.localDefs===true||!target(a,b,ctx))return equal0.call(this,a,b,ctx);
  const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
  const st=this.__projectionClosure??={attempts:0,successes:0,aborts:0,ops:0,projs:0,recs:0,beta:0,lastAbort:null};
  st.attempts++;
  const m=this.__projectionClosureMachine??=machine(this),before={...m.stats};
  try{
    const out=m.prove(a,b);st.successes++;
    for(const q of ["ops","projs","recs","beta"])st[q]+=(out[q]??0)-(before[q]??0);
    return;
  }catch(err){
    if(err!==ABORT&&!(err instanceof Stop)&&!(err instanceof RangeError))throw err;
    st.aborts++;st.lastAbort=m.stats.lastAbort??err?.message??String(err);
    this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    return equal0.call(this,a,b,ctx);
  }
};
