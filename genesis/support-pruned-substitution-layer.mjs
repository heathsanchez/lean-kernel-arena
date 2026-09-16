import {Kernel} from "./kernel-base.mjs";

// Exact support-pruned de-Bruijn substitution.
//
// Requires the compositional __support metadata produced by
// compiled-dynamic-slot-layer.mjs. support(e) is max free index + 1 relative to
// e. When support(e) <= depth, e contains neither the substituted binder nor
// any higher free variable whose index must decrement. The exact substitution
// result is therefore e itself.
//
// Otherwise reproduce retained iterative substitution exactly, with exact
// identity-keyed memoization of completed successes.
const p=Kernel.prototype,run0=p.run;

function cache(k,e,arg){
  k.__supportSubCache??=new WeakMap();
  let byArg=k.__supportSubCache.get(e);
  if(!byArg){byArg=new WeakMap();k.__supportSubCache.set(e,byArg);}
  let byDepth=byArg.get(arg);
  if(!byDepth){byDepth=new Map();byArg.set(arg,byDepth);}
  return byDepth;
}
p.run=function(...args){
  this.__supportSubCache=new WeakMap();
  this.__supportSubStats={pruned:0,cacheHits:0,visits:0,builds:0};
  return run0.apply(this,args);
};

p.substitute=function(root,arg,depth=0){
  this.__supportSubStats??={pruned:0,cacheHits:0,visits:0,builds:0};
  const work=[{kind:"visit",e:root,d:depth}],vals=[];
  while(work.length){
    const f=work.pop();
    if(f.kind==="build"){
      const xs=new Array(f.n);
      for(let i=f.n-1;i>=0;i--)xs[i]=vals.pop();
      let out;
      if(f.tag==="proj")out=this.make("proj",f.name,f.index,xs[0]);
      else out=this.make(f.tag,...xs);
      cache(this,f.e,arg).set(f.d,out);
      this.__supportSubStats.builds++;
      vals.push(out);continue;
    }

    const e=f.e,d=f.d;
    if(!Array.isArray(e))return e;
    const sup=this.__support?.get(e);
    if(sup!==undefined&&sup<=d){
      this.__supportSubStats.pruned++;
      cache(this,e,arg).set(d,e);
      vals.push(e);continue;
    }

    const m=cache(this,e,arg);
    if(m.has(d)){
      this.__supportSubStats.cacheHits++;
      vals.push(m.get(d));continue;
    }

    this.tick();this.__supportSubStats.visits++;
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":
        m.set(d,e);vals.push(e);break;
      case "var":{
        const out=e[1]===d?this.shift(arg,d):e[1]>d?this.make("var",e[1]-1):e;
        m.set(d,out);vals.push(out);break;
      }
      case "pi":case "lam":
        work.push({kind:"build",tag:e[0],n:2,e,d});
        work.push({kind:"visit",e:e[2],d:d+1});
        work.push({kind:"visit",e:e[1],d});break;
      case "app":
        work.push({kind:"build",tag:"app",n:2,e,d});
        work.push({kind:"visit",e:e[2],d});
        work.push({kind:"visit",e:e[1],d});break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2],n:1,e,d});
        work.push({kind:"visit",e:e[3],d});break;
      case "let":
        work.push({kind:"build",tag:"let",n:3,e,d});
        work.push({kind:"visit",e:e[3],d:d+1});
        work.push({kind:"visit",e:e[2],d});
        work.push({kind:"visit",e:e[1],d});break;
      default:this.unknown("substitution-syntax");
    }
  }
  return vals.pop();
};
