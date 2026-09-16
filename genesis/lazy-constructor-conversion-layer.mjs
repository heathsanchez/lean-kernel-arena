import {Kernel,Stop} from "./kernel-base.mjs";

// Transactional lazy constructor conversion.
//
// Instead of asking the retained converter to normalize two large computations,
// chase only weak heads. When both sides expose the same constructor, prove the
// application equal by congruence and continue on its arguments. Successful WHNF
// consequences are cached by exact node identity within the run. No constructor
// injectivity, discrimination, or new reduction rule is assumed.
const p=Kernel.prototype;
const run0=p.run,equal0=p.equal,whnf0=p.whnf;

function ensure(k){
  k.__lazyCtorWhnf??=new WeakMap();
  k.__lazyCtorStats??={attempts:0,successes:0,aborts:0,pairs:0,ctorPairs:0,
    whnfHits:0,whnfStores:0,maxWork:0};
}
function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return{h,args};
}
function kind(k,h){
  if(!Array.isArray(h)||h[0]!=="const")return null;
  return k.env?.get(h[1])?.kind??null;
}
function interesting(k,e){
  if(!Array.isArray(e))return false;
  const s=spine(e),q=kind(k,s.h);
  return q==="def"||q==="rec"||q==="ctor";
}
function cachedWhnf(k,e){
  if(!Array.isArray(e)||k.localDefs===true)return whnf0.call(k,e);
  ensure(k);
  if(k.__lazyCtorWhnf.has(e)){
    k.__lazyCtorStats.whnfHits++;
    return k.__lazyCtorWhnf.get(e);
  }
  const out=whnf0.call(k,e);
  k.__lazyCtorWhnf.set(e,out);
  k.__lazyCtorStats.whnfStores++;
  return out;
}
const ABORT=Symbol("abort");
function prove(k,a,b,ctx){
  const work=[[a,b,ctx]];
  let ctorPairs=0;
  for(let guard=0;work.length&&guard<100000;guard++){
    k.__lazyCtorStats.maxWork=Math.max(k.__lazyCtorStats.maxWork,work.length);
    const [u,v,c]=work.pop();
    k.__lazyCtorStats.pairs++;
    if(u===v||k.same(u,v))continue;

    let x=cachedWhnf(k,u),y=cachedWhnf(k,v);
    if(x===y||k.same(x,y))continue;

    const sx=spine(x),sy=spine(y);
    if(!(Array.isArray(sx.h)&&Array.isArray(sy.h)&&
         sx.h[0]==="const"&&sy.h[0]==="const"&&
         sx.h[1]===sy.h[1]&&sx.args.length===sy.args.length))
      throw ABORT;

    const q=kind(k,sx.h);
    if(q!=="ctor")throw ABORT;

    // Same constructor application: congruence is sufficient for equality.
    // Universe instances on the head must also match exactly/definitionally.
    const ux=sx.h[2]??[],uy=sy.h[2]??[];
    if(ux.length!==uy.length)throw ABORT;
    for(let i=0;i<ux.length;i++)if(JSON.stringify(ux[i])!==JSON.stringify(uy[i]))throw ABORT;

    ctorPairs++;k.__lazyCtorStats.ctorPairs++;
    for(let i=sx.args.length-1;i>=0;i--)work.push([sx.args[i],sy.args[i],c]);
  }
  if(work.length)throw ABORT;
  if(ctorPairs===0)throw ABORT;
}

p.run=function(...args){
  this.__lazyCtorWhnf=new WeakMap();
  this.__lazyCtorStats={attempts:0,successes:0,aborts:0,pairs:0,ctorPairs:0,
    whnfHits:0,whnfStores:0,maxWork:0};
  this.__lazyCtorGuard=0;
  return run0.apply(this,args);
};

p.equal=function(a,b,ctx=[]){
  ensure(this);
  if(this.localDefs===true||this.__lazyCtorGuard>0||(!interesting(this,a)&&!interesting(this,b)))
    return equal0.call(this,a,b,ctx);

  this.__lazyCtorStats.attempts++;
  const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
  this.__lazyCtorGuard++;
  try{
    prove(this,a,b,ctx);
    this.__lazyCtorStats.successes++;
    return;
  }catch(err){
    if(err!==ABORT && !(err instanceof Stop) && !(err instanceof RangeError))throw err;
    this.__lazyCtorStats.aborts++;
    this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    return equal0.call(this,a,b,ctx);
  }finally{
    this.__lazyCtorGuard--;
  }
};
