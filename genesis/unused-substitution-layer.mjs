import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,sub0=p.substitute;

function ensure(k){
  k.__unusedOccurrence??=new WeakMap();
  k.__unusedDrop??=new WeakMap();
  k.__unusedStats??={queries:0,provedUnused:0,occurrenceHits:0,dropHits:0,drops:0};
}
function depthMap(wm,e){
  let m=wm.get(e);if(!m){m=new Map();wm.set(e,m);}return m;
}
function occurs(k,root,depth){
  ensure(k);k.__unusedStats.queries++;
  const rm=depthMap(k.__unusedOccurrence,root);
  if(rm.has(depth)){k.__unusedStats.occurrenceHits++;return rm.get(depth);}
  const work=[{e:root,d:depth,post:false}],vals=[];
  while(work.length){
    const f=work.pop(),e=f.e,d=f.d,m=depthMap(k.__unusedOccurrence,e);
    if(m.has(d)){k.__unusedStats.occurrenceHits++;vals.push(m.get(d));continue;}
    k.tick();
    if(f.post){
      let n=f.n,yes=false;while(n-->0)yes=vals.pop()||yes;
      m.set(d,yes);vals.push(yes);continue;
    }
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":m.set(d,false);vals.push(false);break;
      case "var":{const yes=e[1]===d;m.set(d,yes);vals.push(yes);break;}
      case "pi":case "lam":
        work.push({e,d,post:true,n:2});
        work.push({e:e[2],d:d+1,post:false});work.push({e:e[1],d,post:false});break;
      case "app":
        work.push({e,d,post:true,n:2});
        work.push({e:e[2],d,post:false});work.push({e:e[1],d,post:false});break;
      case "proj":
        work.push({e,d,post:true,n:1});work.push({e:e[3],d,post:false});break;
      case "let":
        work.push({e,d,post:true,n:3});
        work.push({e:e[3],d:d+1,post:false});work.push({e:e[2],d,post:false});work.push({e:e[1],d,post:false});break;
      default:m.set(d,true);vals.push(true);break;
    }
  }
  return vals.pop();
}
function dropUnused(k,root,depth){
  ensure(k);
  const rm=depthMap(k.__unusedDrop,root);
  if(rm.has(depth)){k.__unusedStats.dropHits++;return rm.get(depth);}
  const work=[{e:root,d:depth,post:false}],vals=[];
  while(work.length){
    const f=work.pop(),e=f.e,d=f.d,m=depthMap(k.__unusedDrop,e);
    if(m.has(d)){k.__unusedStats.dropHits++;vals.push(m.get(d));continue;}
    if(f.post){
      const xs=new Array(f.n);for(let i=f.n-1;i>=0;i--)xs[i]=vals.pop();
      let out;if(f.tag==="proj")out=k.make("proj",f.name,f.index,xs[0]);else out=k.make(f.tag,...xs);
      m.set(d,out);vals.push(out);continue;
    }
    k.tick();
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":m.set(d,e);vals.push(e);break;
      case "var":{
        const out=e[1]>d?k.make("var",e[1]-1):e;m.set(d,out);vals.push(out);break;
      }
      case "pi":case "lam":
        work.push({e,d,post:true,n:2,tag:e[0]});
        work.push({e:e[2],d:d+1,post:false});work.push({e:e[1],d,post:false});break;
      case "app":
        work.push({e,d,post:true,n:2,tag:"app"});
        work.push({e:e[2],d,post:false});work.push({e:e[1],d,post:false});break;
      case "proj":
        work.push({e,d,post:true,n:1,tag:"proj",name:e[1],index:e[2]});work.push({e:e[3],d,post:false});break;
      case "let":
        work.push({e,d,post:true,n:3,tag:"let"});
        work.push({e:e[3],d:d+1,post:false});work.push({e:e[2],d,post:false});work.push({e:e[1],d,post:false});break;
      default:return sub0.call(k,root,["sort",0],depth);
    }
  }
  const out=vals.pop();rm.set(depth,out);k.__unusedStats.drops++;return out;
}
p.run=function(...args){
  this.__unusedOccurrence=new WeakMap();this.__unusedDrop=new WeakMap();
  this.__unusedStats={queries:0,provedUnused:0,occurrenceHits:0,dropHits:0,drops:0};
  return run0.apply(this,args);
};
p.substitute=function(e,arg,depth=0){
  if(Array.isArray(e)&&occurs(this,e,depth)===false){
    this.__unusedStats.provedUnused++;return dropUnused(this,e,depth);
  }
  return sub0.call(this,e,arg,depth);
};
