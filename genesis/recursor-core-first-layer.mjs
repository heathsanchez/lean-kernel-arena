import {Kernel} from "./kernel-base.mjs";

// Exact evaluation-order refinement for recursors with extra arguments.
// Reduce the fully saturated recursor core (through its major premise) to WHNF
// before attaching arguments beyond the recursor's semantic arity.
//
// This is extensionally the same iota/beta reduction sequence, but prevents an
// unrelated extra argument from being substituted through the closed recursor
// spine at every recursive step. Successful core WHNFs are cached by exact
// canonical core-node identity within the current run. LocalDef execution is
// excluded because its WHNF can depend on the active local context.
const p=Kernel.prototype,run0=p.run,whnf0=p.whnf;

function flatten(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function ensure(k){
  k.__recCoreWhnf??=new WeakMap();
  k.__recCoreStats??={splits:0,hits:0,stores:0,reentries:0};
}

p.run=function(...args){
  this.__recCoreWhnf=new WeakMap();
  this.__recCoreStats={splits:0,hits:0,stores:0,reentries:0};
  this.__recCoreGuard=0;
  return run0.apply(this,args);
};

p.whnf=function(e){
  ensure(this);
  if(this.localDefs===true||!Array.isArray(e)||e[0]!=="app"||this.__recCoreGuard>0)
    return whnf0.call(this,e);

  const {h,args}=flatten(e);
  if(!Array.isArray(h)||h[0]!=="const")return whnf0.call(this,e);
  const rd=this.env?.get(h[1]);
  if(rd?.kind!=="rec")return whnf0.call(this,e);

  const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
  if(args.length<=total)return whnf0.call(this,e);

  this.__recCoreStats.splits++;
  let core=this.appN(h,args.slice(0,total)),reduced;
  if(this.__recCoreWhnf.has(core)){
    this.__recCoreStats.hits++;
    reduced=this.__recCoreWhnf.get(core);
  }else{
    this.__recCoreGuard++;
    try{reduced=whnf0.call(this,core);}
    finally{this.__recCoreGuard--;}
    this.__recCoreWhnf.set(core,reduced);
    this.__recCoreStats.stores++;
  }

  let out=reduced;
  for(const a of args.slice(total))out=this.make("app",out,a);
  this.__recCoreStats.reentries++;
  return this.whnf(out);
};
