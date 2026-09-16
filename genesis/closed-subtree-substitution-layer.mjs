import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,sub0=p.substitute;

function ensure(k){
  k.__closedSubstCache??=new WeakMap();
  k.__closedSubstStats??={queries:0,cacheHits:0,closedSkips:0,visited:0,fallbacks:0};
}
function cacheMap(k,e,arg){
  let byArg=k.__closedSubstCache.get(e);
  if(!byArg){byArg=new WeakMap();k.__closedSubstCache.set(e,byArg);}
  let byDepth=byArg.get(arg);
  if(!byDepth){byDepth=new Map();byArg.set(arg,byDepth);}
  return byDepth;
}

p.run=function(...args){
  this.__closedSubstCache=new WeakMap();
  this.__closedSubstStats={queries:0,cacheHits:0,closedSkips:0,visited:0,fallbacks:0};
  return run0.apply(this,args);
};

p.substitute=function(root,arg,depth=0){
  ensure(this);
  if(!Array.isArray(root)||!Array.isArray(arg))return sub0.call(this,root,arg,depth);
  this.__closedSubstStats.queries++;

  const work=[{kind:"visit",e:root,depth}],vals=[];
  while(work.length){
    const f=work.pop();
    if(f.kind==="build"){
      let out;
      if(f.tag==="proj")out=this.make("proj",f.name,f.index,vals.pop());
      else{
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--)xs[i]=vals.pop();
        out=this.make(f.tag,...xs);
      }
      cacheMap(this,f.e,arg).set(f.depth,out);
      vals.push(out);
      continue;
    }

    const e=f.e,d=f.depth,cache=cacheMap(this,e,arg);
    if(cache.has(d)){
      this.__closedSubstStats.cacheHits++;
      vals.push(cache.get(d));continue;
    }

    const sup=this.__support?.get(e);
    if(sup===0){
      this.__closedSubstStats.closedSkips++;
      cache.set(d,e);vals.push(e);continue;
    }

    if(sup===undefined){
      this.__closedSubstStats.fallbacks++;
      const out=sub0.call(this,e,arg,d);
      cache.set(d,out);vals.push(out);continue;
    }

    this.tick();this.__closedSubstStats.visited++;
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":
        cache.set(d,e);vals.push(e);break;
      case "var":{
        const out=e[1]===d?this.shift(arg,d):e[1]>d?this.make("var",e[1]-1):e;
        cache.set(d,out);vals.push(out);break;
      }
      case "pi":case "lam":
        work.push({kind:"build",tag:e[0],n:2,e,depth:d});
        work.push({kind:"visit",e:e[2],depth:d+1});
        work.push({kind:"visit",e:e[1],depth:d});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2,e,depth:d});
        work.push({kind:"visit",e:e[2],depth:d});
        work.push({kind:"visit",e:e[1],depth:d});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2],e,depth:d});
        work.push({kind:"visit",e:e[3],depth:d});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3,e,depth:d});
        work.push({kind:"visit",e:e[3],depth:d+1});
        work.push({kind:"visit",e:e[2],depth:d});
        work.push({kind:"visit",e:e[1],depth:d});
        break;
      default:{
        this.__closedSubstStats.fallbacks++;
        const out=sub0.call(this,e,arg,d);
        cache.set(d,out);vals.push(out);break;
      }
    }
  }
  return vals.pop();
};
