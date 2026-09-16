import {Kernel,Stop} from "./kernel-base.mjs";

// Closed monomorphic closure conversion separator.
// It proves equality only by retained definitional reductions and congruence,
// while substitutions are represented as environments instead of materialized
// syntax. Anything outside the deliberately small envelope aborts and replays
// the retained converter from the exact semantic snapshot.
const p=Kernel.prototype,equal0=p.equal,run0=p.run;
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
  const termClosures=new WeakMap(),envCons=new WeakMap(),whnfCache=new WeakMap(),derefCache=new WeakMap(),appSpineCache=new WeakMap(),eqSuccess=new WeakMap(),stateWhnfCache=new Map(),iteratorInfoCache=new WeakMap(),iteratorCanonical=new Map();
  let closureNext=1,attemptOps=0;
  const stats={ops:0,beta:0,defs:0,recs:0,vars:0,apps:0,whnfHits:0,whnfStores:0,
    ctorPairs:0,rigidPairs:0,maxEnv:0,maxArgs:0,derefHits:0,derefStores:0,derefSteps:0,appSpineHits:0,appSpineStores:0,appSpineNodes:0,stateHits:0,stateStores:0,iteratorHits:0,iteratorStores:0,iteratorChecks:0,eqHits:0,eqStores:0,lastAbort:null};

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
    k.tick();stats.ops++;attemptOps++;
    if(attemptOps>900000){stats.lastAbort="op-cap";throw ABORT;}
  }
  function sameLevels(a,b){return JSON.stringify(a??[])===JSON.stringify(b??[]);}

  function deref(start){
    const cached=derefCache.get(start);
    if(cached!==undefined){stats.derefHits++;return cached;}
    let cl=start;
    const path=[];
    for(let guard=0;guard<10000;guard++){
      const t=cl.term,env=cl.env;
      if(!Array.isArray(t)||t[0]!=="var")break;
      const old=derefCache.get(cl);
      if(old!==undefined){
        stats.derefHits++;
        cl=old;
        break;
      }
      if(t[1]>=env.length){stats.lastAbort="free-var";throw ABORT;}
      k.tick();stats.ops++;attemptOps++;stats.vars++;stats.derefSteps++;
      if(attemptOps>900000){stats.lastAbort="op-cap";throw ABORT;}
      path.push(cl);
      cl=env[t[1]];
    }
    for(const q of path){derefCache.set(q,cl);stats.derefStores++;}
    return cl;
  }

  function appSpine(root){
    const old=appSpineCache.get(root);
    if(old!==undefined){stats.appSpineHits++;return old;}
    let h=root;
    const rev=[];
    while(Array.isArray(h)&&h[0]==="app"){
      bump();
      stats.apps++;stats.appSpineNodes++;
      rev.push(h[2]);h=h[1];
    }
    const out={head:h,args:Object.freeze(rev.reverse())};
    appSpineCache.set(root,out);stats.appSpineStores++;
    return out;
  }

  function iteratorInfo(d){
    if(iteratorInfoCache.has(d))return iteratorInfoCache.get(d);
    let info=null;
    try{
      if((d.levelParams??[]).length!==0)throw 0;
      let e=d.value;
      if(!Array.isArray(e)||e[0]!=="lam")throw 0;
      e=e[2];
      if(!Array.isArray(e)||e[0]!=="lam")throw 0;
      e=e[2];

      const rs=rawSpine(e),rh=rs.h,rargs=rs.args;
      if(!Array.isArray(rh)||rh[0]!=="const")throw 0;
      const rd=k.env.get(rh[1]);
      if(rd?.kind!=="rec"||rd.numParams!==0||rd.numIndices!==0||rd.numMinors!==2||
         (rd.levelParams??[]).length!==0)throw 0;
      if(rargs.length!==4)throw 0;
      const ind=k.env.get(rd.induct);
      if(ind?.kind!=="inductive"||ind.numParams!==0||ind.numIndices!==0||
         (ind.levelParams??[]).length!==0||!Array.isArray(ind.ctors)||ind.ctors.length!==2)throw 0;

      const ctors=ind.ctors.map(n=>k.env.get(n));
      const zi=ctors.findIndex(q=>q?.kind==="ctor"&&q.numFields===0);
      const si=ctors.findIndex(q=>q?.kind==="ctor"&&q.numFields===1);
      if(zi<0||si<0||zi===si)throw 0;
      const zero=ctors[zi],succ=ctors[si];
      if((zero.levelParams??[]).length!==0||(succ.levelParams??[]).length!==0||
         zero.numParams!==0||succ.numParams!==0)throw 0;

      // motive, then one minor per constructor, then major.
      const base=rargs[1+zi],step=rargs[1+si],major=rargs[3];
      if(!Array.isArray(base)||base[0]!=="var"||base[1]!==0)throw 0;
      if(!Array.isArray(major)||major[0]!=="var"||major[1]!==1)throw 0;

      // Recursive unary constructor minor: fun _ ih => Succ ih.
      if(!Array.isArray(step)||step[0]!=="lam")throw 0;
      let sb=step[2];
      if(!Array.isArray(sb)||sb[0]!=="lam")throw 0;
      sb=sb[2];
      const ss=rawSpine(sb);
      if(!Array.isArray(ss.h)||ss.h[0]!=="const"||ss.h[1]!==succ.name||
         ss.args.length!==1||!Array.isArray(ss.args[0])||ss.args[0][0]!=="var"||ss.args[0][1]!==0)
        throw 0;

      info={defName:d.name,induct:ind.name,zero:zero.name,succ:succ.name};
    }catch(_){info=null;}
    iteratorInfoCache.set(d,info);
    return info;
  }

  function constView(v,name,arity){
    const t=v?.head?.term;
    return Array.isArray(t)&&t[0]==="const"&&t[1]===name&&v.args.length===arity;
  }

  function canonicalSet(info){
    let s=iteratorCanonical.get(info.defName);
    if(!s){s=new WeakSet();iteratorCanonical.set(info.defName,s);}
    return s;
  }

  function certifyCanonical(info,a,depth=0){
    const done=canonicalSet(info);
    if(done.has(a)){stats.iteratorHits++;return;}
    if(depth>6000){stats.lastAbort="iterator-depth";throw ABORT;}
    stats.iteratorChecks++;
    const v=whnf(a,depth+1);
    if(constView(v,info.zero,0)){
      done.add(a);stats.iteratorStores++;return;
    }
    if(constView(v,info.succ,1)){
      certifyCanonical(info,v.args[0],depth+1);
      done.add(a);stats.iteratorStores++;return;
    }
    stats.lastAbort="iterator-major-not-canonical";throw ABORT;
  }

  function isSuccZero(info,b,depth){
    const v=whnf(b,depth+1);
    if(!constView(v,info.succ,1))return false;
    const z=whnf(v.args[0],depth+1);
    return constView(z,info.zero,0);
  }

  function stateKey(head,args){
    let s=String(head.__id)+"|";
    for(let i=0;i<args.length;i++)s+=(i?",":"")+String(args[i].__id);
    return s;
  }
  function finishWhnf(start,out,pendingStates){
    whnfCache.set(start,out);stats.whnfStores++;
    for(const key of pendingStates){
      if(!stateWhnfCache.has(key)){stateWhnfCache.set(key,out);stats.stateStores++;}
    }
    return out;
  }

  function whnf(start,depth=0){
    if(depth>6000){stats.lastAbort="depth";throw ABORT;}
    const old=whnfCache.get(start);
    if(old!==undefined){stats.whnfHits++;return old;}

    let cl=start,args=[],pendingStates=[];
    for(let guard=0;guard<200000;guard++){
      cl=deref(cl);
      stats.maxEnv=Math.max(stats.maxEnv,cl.env.length);
      stats.maxArgs=Math.max(stats.maxArgs,args.length);
      const t=cl.term,env=cl.env;
      if(!Array.isArray(t)){stats.lastAbort="non-term";throw ABORT;}

      if(t[0]==="app"){
        k.need("application");
        const sp=appSpine(t),xs=new Array(sp.args.length);
        for(let i=0;i<sp.args.length;i++)xs[i]=C(sp.args[i],env);
        args=xs.concat(args);
        cl=C(sp.head,env);
        continue;
      }

      bump();
      if(t[0]==="let"){
        k.need("reduction");
        cl=C(t[3],cons(C(t[2],env),env));continue;
      }
      if(t[0]==="lam"&&args.length){
        k.need("reduction");stats.beta++;
        cl=C(t[2],cons(args.shift(),env));continue;
      }
      if(t[0]==="proj"){stats.lastAbort="projection";throw ABORT;}
      if(t[0]==="nat"||t[0]==="strlit"||t[0]==="sort"||t[0]==="pi"||t[0]==="lam"){
        const out={head:cl,args:Object.freeze(args.slice())};
        return finishWhnf(start,out,pendingStates);
      }
      if(t[0]!=="const"){stats.lastAbort="whnf-syntax:"+t[0];throw ABORT;}

      k.need("declarations");
      const d=k.env.get(t[1]);if(!d)k.reject("undeclared-constant");

      // Verified unary iterator consequence. For a structurally certified
      // iterator f a b = rec b (fun _ ih => Succ ih) a, and a concrete major
      // proven canonical constructor-by-constructor, f a (Succ Zero) has WHNF
      // Succ a. No opaque/stuck major is assumed canonical.
      if(d.kind==="def"&&args.length===2){
        const info=iteratorInfo(d);
        if(info!==null&&isSuccZero(info,args[1],depth)){
          certifyCanonical(info,args[0],depth);
          const succHead=C(["const",info.succ],EMPTY);
          const out={head:succHead,args:Object.freeze([args[0]])};
          stats.iteratorHits++;
          return finishWhnf(start,out,pendingStates);
        }
      }

      if((d.kind==="def"||d.kind==="rec")&&args.length){
        const key=stateKey(cl,args),hit=stateWhnfCache.get(key);
        if(hit!==undefined){
          stats.stateHits++;
          whnfCache.set(start,hit);stats.whnfStores++;
          return hit;
        }
        if(pendingStates.length===0||pendingStates[pendingStates.length-1]!==key)
          pendingStates.push(key);
      }

      if(d.kind==="def"){
        k.need("reduction");stats.defs++;
        const body=k.instantiateDeclaration(t,d.value);
        cl=C(body,EMPTY);continue;
      }
      if(d.kind==="rec"&&args.length>=d.numParams+1+d.numMinors+d.numIndices+1){
        // Deliberate separator boundary: the shared-DAG family is non-indexed
        // and parameter-free. Anything broader is left to retained semantics.
        if(d.numParams!==0||d.numIndices!==0){stats.lastAbort="param-or-indexed-rec";throw ABORT;}
        const total=1+d.numMinors+1,major=whnf(args[total-1],depth+1);
        const mh=major.head.term,md=Array.isArray(mh)&&mh[0]==="const"?k.env.get(mh[1]):null;
        if(md?.kind==="ctor"&&md.induct===d.induct&&major.args.length===md.numFields){
          const rule=d.rules.find(r=>r.ctor===md.name);
          if(!rule){stats.lastAbort="missing-rule";throw ABORT;}
          k.need("inductive-reduction");k.need("reduction");stats.recs++;
          const rhs=k.instantiateDeclaration(t,rule.rhs);
          const prefix=args.slice(0,1+d.numMinors),extras=args.slice(total);
          args=prefix.concat(major.args,extras);
          cl=C(rhs,EMPTY);continue;
        }
      }

      const out={head:cl,args:Object.freeze(args.slice())};
      return finishWhnf(start,out,pendingStates);
    }
    stats.lastAbort="whnf-loop";throw ABORT;
  }

  function hasEq(a,b){
    const s=eqSuccess.get(a);return s?.has(b)===true;
  }
  function storeEq(a,b){
    let s=eqSuccess.get(a);if(!s){s=new WeakSet();eqSuccess.set(a,s);}s.add(b);
    let t=eqSuccess.get(b);if(!t){t=new WeakSet();eqSuccess.set(b,t);}t.add(a);
    stats.eqStores++;
  }
  function prove(a,b){
    attemptOps=0;stats.lastAbort=null;
    const ca=C(a,EMPTY),cb=C(b,EMPTY);
    if(hasEq(ca,cb)){stats.eqHits++;return stats;}
    const ctorBefore=stats.ctorPairs;
    const work=[[ca,cb]];
    for(let guard=0;work.length&&guard<200000;guard++){
      const [ca,cb]=work.pop();
      if(ca===cb)continue;
      const x=whnf(ca),y=whnf(cb);
      if(x.head===y.head&&x.args.length===y.args.length&&x.args.every((q,i)=>q===y.args[i]))continue;

      const a0=x.head.term,b0=y.head.term;
      if(!Array.isArray(a0)||!Array.isArray(b0)||a0[0]!==b0[0]){stats.lastAbort="head-tag";throw ABORT;}

      if(a0[0]==="const"){
        if(a0[1]!==b0[1]||!sameLevels(a0[2],b0[2])||x.args.length!==y.args.length){stats.lastAbort="const-mismatch";throw ABORT;}
        const d=k.env.get(a0[1]);
        if(d?.kind==="ctor")stats.ctorPairs++;else stats.rigidPairs++;
        for(let i=x.args.length-1;i>=0;i--)work.push([x.args[i],y.args[i]]);
        continue;
      }
      if(a0[0]==="nat"||a0[0]==="strlit"){
        if(a0[1]!==b0[1]||x.args.length||y.args.length){stats.lastAbort="literal-mismatch";throw ABORT;}
        stats.rigidPairs++;continue;
      }
      if(a0[0]==="sort"){
        if(JSON.stringify(a0[1])!==JSON.stringify(b0[1])||x.args.length||y.args.length){stats.lastAbort="sort-mismatch";throw ABORT;}
        stats.rigidPairs++;continue;
      }
      stats.lastAbort="unsupported-head:"+a0[0];throw ABORT;
    }
    if(work.length||stats.ctorPairs===ctorBefore){stats.lastAbort=work.length?"work-left":"no-ctor";throw ABORT;}
    storeEq(ca,cb);
    return stats;
  }
  return {prove,stats};
}

p.run=function(...args){
  this.__closedGlobalBudget=this.budget;
  this.__closedMachine=null;
  this.__closedClosureStats={attempts:0,successes:0,aborts:0,ops:0,ctorPairs:0,whnfHits:0,recs:0,beta:0,
    eqHits:0,eqStores:0,events:[]};
  return run0.apply(this,args);
};

p.equal=function(a,b,ctx=[]){
  if(this.localDefs===true||!target(this,a,b,ctx))return equal0.call(this,a,b,ctx);
  const describe=e=>{
    const s=rawSpine(e),h=s.h;
    return {tag:e?.[0]??typeof e,args:s.args.length,
      head:Array.isArray(h)&&h[0]==="const"?h[1]:(h?.[0]??typeof h),
      kind:Array.isArray(h)&&h[0]==="const"?(this.env?.get(h[1])?.kind??null):null};
  };
  this.__closedClosureStats??={attempts:0,successes:0,aborts:0,ops:0,ctorPairs:0,whnfHits:0,recs:0,beta:0,eqHits:0,eqStores:0};
  this.__closedClosureStats.attempts++;
  const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
  const globalBudget=this.__closedGlobalBudget??this.budget;
  if(this.budget<globalBudget)this.budget=globalBudget;
  const event={step:snap.steps,decl:this.currentDeclaration??null,a:describe(a),b:describe(b),
    inheritedBudget:snap.budget,proofBudget:this.budget};
  const m=this.__closedMachine??=machine(this);
  const before={};
  const successKeys=["ops","ctorPairs","whnfHits","recs","beta","eqHits","eqStores"];
  const diagnosticKeys=["defs","vars","apps","whnfStores","derefHits","derefStores","derefSteps","appSpineHits","appSpineStores","appSpineNodes","stateHits","stateStores","iteratorHits","iteratorStores","iteratorChecks"];
  for(const q of successKeys.concat(diagnosticKeys))before[q]=m.stats[q]??0;
  try{
    const st=m.prove(a,b);
    this.__closedClosureStats.successes++;
    for(const q of successKeys)this.__closedClosureStats[q]+=(st[q]??0)-before[q];
    event.outcome="success";event.endStep=this.steps;event.delta=this.steps-snap.steps;
    event.ops=(st.ops??0)-before.ops;event.beta=(st.beta??0)-before.beta;
    event.recs=(st.recs??0)-before.recs;event.vars=(st.vars??0)-before.vars;
    event.eqHits=(st.eqHits??0)-before.eqHits;
    this.__closedClosureStats.events.push(event);
    return;
  }catch(err){
    if(err!==ABORT&&!(err instanceof Stop)&&!(err instanceof RangeError))throw err;
    this.__closedClosureStats.aborts++;
    this.__closedClosureStats.abortOps=(this.__closedClosureStats.abortOps??0)+((m.stats.ops??0)-(before.ops??0));
    for(const q of ["beta","defs","recs","vars","apps","whnfHits","whnfStores","derefHits","derefStores","derefSteps","appSpineHits","appSpineStores","appSpineNodes","stateHits","stateStores","iteratorHits","iteratorStores","iteratorChecks"]){
      const key="abort"+q[0].toUpperCase()+q.slice(1);
      const b=q in before?(before[q]??0):0;
      this.__closedClosureStats[key]=(this.__closedClosureStats[key]??0)+((m.stats[q]??0)-b);
    }
    this.__closedClosureStats.lastAbort=m.stats.lastAbort??"unknown";
    event.outcome="abort";event.error=err===ABORT?(m.stats.lastAbort??"abort"):(err?.message??String(err));
    event.errorStatus=err?.status??null;event.attemptSteps=this.steps-snap.steps;
    event.ops=(m.stats.ops??0)-before.ops;event.beta=(m.stats.beta??0)-before.beta;
    event.recs=(m.stats.recs??0)-before.recs;event.vars=(m.stats.vars??0)-before.vars;
    this.__closedClosureStats.events.push(event);
    this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    return equal0.call(this,a,b,ctx);
  }
};
