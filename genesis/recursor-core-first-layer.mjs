import {Kernel} from "./kernel-base.mjs";

// Stack-safe exact evaluation-order refinement for recursors with extra args.
// Repeatedly:
//   1. reduce the saturated recursor core through its major premise,
//   2. beta-apply only the arguments beyond semantic recursor arity,
//   3. continue if that exposes another saturated recursor-with-extra.
// No JS recursion is introduced by this layer.
const p=Kernel.prototype,run0=p.run,whnf0=p.whnf;

function flatten(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function ensure(k){
  k.__recCoreWhnf??=new WeakMap();
  k.__recCoreStats??={splits:0,hits:0,stores:0,iterations:0,manualBeta:0,blocked:0};
}
function target(k,e){
  if(!Array.isArray(e)||e[0]!=="app")return null;
  const {h,args}=flatten(e);
  if(!Array.isArray(h)||h[0]!=="const")return null;
  const rd=k.env?.get(h[1]);
  if(rd?.kind!=="rec")return null;
  const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
  if(args.length<=total)return null;
  return {h,args,rd,total};
}
function retained(k,e){
  k.__recCoreGuard=(k.__recCoreGuard??0)+1;
  try{return whnf0.call(k,e);}
  finally{k.__recCoreGuard--;}
}

p.run=function(...args){
  this.__recCoreWhnf=new WeakMap();
  this.__recCoreStats={splits:0,hits:0,stores:0,iterations:0,manualBeta:0,blocked:0};
  this.__recCoreGuard=0;
  return run0.apply(this,args);
};

p.whnf=function(e){
  ensure(this);
  if(this.localDefs===true||this.__recCoreGuard>0)return whnf0.call(this,e);

  let cur=e,entered=false;
  for(let guard=0;guard<100000;guard++){
    const q=target(this,cur);
    if(q===null){
      return entered?retained(this,cur):whnf0.call(this,e);
    }
    entered=true;
    this.__recCoreStats.splits++;
    this.__recCoreStats.iterations++;

    let core=this.appN(q.h,q.args.slice(0,q.total)),reduced;
    if(this.__recCoreWhnf.has(core)){
      this.__recCoreStats.hits++;
      reduced=this.__recCoreWhnf.get(core);
    }else{
      reduced=retained(this,core);
      if(reduced===core){
        this.__recCoreStats.blocked++;
        return retained(this,cur);
      }
      this.__recCoreWhnf.set(core,reduced);
      this.__recCoreStats.stores++;
    }

    const extras=q.args.slice(q.total);
    let out=reduced,i=0;
    while(i<extras.length&&Array.isArray(out)&&out[0]==="lam"){
      this.tick();this.need("application");this.need("reduction");
      out=this.substitute(out[2],extras[i++],0);
      this.__recCoreStats.manualBeta++;
    }
    for(;i<extras.length;i++)out=this.make("app",out,extras[i]);
    cur=out;
  }
  this.unknown("recursor-extra-iteration-budget");
};
