import {Kernel} from "./kernel-base.mjs";

// Exact compositional free-support metadata + residual-specific one-slot beta
// substitution. The metadata is derived while already-validated input DAGs are
// visited and propagated O(1) through every later make(). No semantic equality,
// guessed closedness, or problem identity is used.
//
// For the measured residual shape
//   ((((h c1) c2) c3) c4) d
// the left four-argument prefix is certified support=0. Therefore exact
// de-Bruijn substitution is
//   app(prefix, substitute(d,arg))
// and the large closed prefix is reused by pointer identity.
const p=Kernel.prototype;
const run0=p.run,validate0=p.validate,make0=p.make,sub0=p.substitute;

function ensure(k){
  k.__support??=new WeakMap();
  k.__slotStats??={seedVisits:0,makeKnown:0,makeUnknown:0,queries:0,hits:0,
    dynamicNodes:0,prefixReused:0};
}
function get(k,e){return Array.isArray(e)?k.__support.get(e):0;}
function derive(k,e){
  if(!Array.isArray(e))return 0;
  const old=k.__support.get(e);if(old!==undefined)return old;
  let n;
  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":n=0;break;
    case "var":n=Number.isSafeInteger(e[1])&&e[1]>=0?e[1]+1:undefined;break;
    case "app":{
      const a=get(k,e[1]),b=get(k,e[2]);if(a!==undefined&&b!==undefined)n=Math.max(a,b);break;
    }
    case "proj":n=get(k,e[3]);break;
    case "pi":case "lam":{
      const a=get(k,e[1]),b=get(k,e[2]);
      if(a!==undefined&&b!==undefined)n=Math.max(a,Math.max(0,b-1));break;
    }
    case "let":{
      const a=get(k,e[1]),v=get(k,e[2]),b=get(k,e[3]);
      if(a!==undefined&&v!==undefined&&b!==undefined)n=Math.max(a,v,Math.max(0,b-1));break;
    }
  }
  if(n!==undefined)k.__support.set(e,n);
  return n;
}
function seed(k,root){
  ensure(k);
  if(!Array.isArray(root)||k.__support.has(root))return;
  const work=[{e:root,post:false}];
  while(work.length){
    const f=work.pop(),e=f.e;
    if(!Array.isArray(e)||k.__support.has(e))continue;
    if(f.post){derive(k,e);k.__slotStats.seedVisits++;continue;}
    work.push({e,post:true});
    switch(e[0]){
      case "app":
        work.push({e:e[2],post:false},{e:e[1],post:false});break;
      case "proj":work.push({e:e[3],post:false});break;
      case "pi":case "lam":
        work.push({e:e[2],post:false},{e:e[1],post:false});break;
      case "let":
        work.push({e:e[3],post:false},{e:e[2],post:false},{e:e[1],post:false});break;
    }
  }
}
function fiveArgRoot(e){
  let x=e,n=0;
  while(n<6&&Array.isArray(x)&&x[0]==="app"){n++;x=x[1];}
  return n===5;
}
function tinyNodes(e,cap=64){
  if(!Array.isArray(e))return 0;
  let n=0,work=[e];
  while(work.length&&n<=cap){
    const x=work.pop();if(!Array.isArray(x))continue;n++;
    if(x[0]==="app"){work.push(x[1],x[2]);}
    else if(x[0]==="proj")work.push(x[3]);
    else if(x[0]==="pi"||x[0]==="lam")work.push(x[1],x[2]);
    else if(x[0]==="let")work.push(x[1],x[2],x[3]);
  }
  return n;
}

p.run=function(...args){
  this.__support=new WeakMap();
  this.__slotStats={seedVisits:0,makeKnown:0,makeUnknown:0,queries:0,hits:0,
    dynamicNodes:0,prefixReused:0};
  return run0.apply(this,args);
};

p.validate=function(root){
  const out=validate0.call(this,root);
  seed(this,root);
  return out;
};

p.make=function(...xs){
  ensure(this);
  const out=make0.apply(this,xs);
  if(Array.isArray(out)){
    const n=derive(this,out);
    if(n===undefined)this.__slotStats.makeUnknown++;
    else this.__slotStats.makeKnown++;
  }
  return out;
};

p.substitute=function(root,arg,depth=0){
  ensure(this);
  if(depth===0&&Array.isArray(root)&&root[0]==="app"&&fiveArgRoot(root)){
    this.__slotStats.queries++;
    const prefix=root[1],ps=get(this,prefix),ds=get(this,root[2]);
    if(ps===0&&ds!==undefined&&ds>0){
      this.__slotStats.hits++;
      this.__slotStats.prefixReused++;
      this.__slotStats.dynamicNodes+=tinyNodes(root[2]);
      const d=sub0.call(this,root[2],arg,0);
      return this.make("app",prefix,d);
    }
  }
  return sub0.call(this,root,arg,depth);
};
