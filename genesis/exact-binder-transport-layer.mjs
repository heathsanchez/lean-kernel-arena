import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,shift0=p.shift,sub0=p.substitute;

function ensure(k){
  k.__binderShiftMemo??=new WeakMap();
  k.__binderSubstMemo??=new WeakMap();
  k.__looseRangeMemo??=new WeakMap();
  k.__binderStats??={shiftHits:0,shiftMisses:0,substHits:0,substMisses:0,rangeHits:0,rangeMisses:0,rangeSkips:0};
}

function looseRange(k,root){
  const work=[{e:root}],vals=[];
  while(work.length){
    const f=work.pop(),e=f.e;
    if(f.build){
      const xs=vals.splice(vals.length-f.n,f.n);
      let r;
      switch(e[0]){
        case "app": r=Math.max(xs[0],xs[1]);break;
        case "proj": r=xs[0];break;
        case "pi": case "lam": r=Math.max(xs[0],Math.max(0,xs[1]-1));break;
        case "let": r=Math.max(xs[0],xs[1],Math.max(0,xs[2]-1));break;
      }
      k.__looseRangeMemo.set(e,r);vals.push(r);continue;
    }
    if(!Array.isArray(e)){vals.push(Number.POSITIVE_INFINITY);continue;}
    const hit=k.__looseRangeMemo.get(e);
    if(hit!==undefined){k.__binderStats.rangeHits++;vals.push(hit);continue;}
    k.__binderStats.rangeMisses++;
    let r,children;
    switch(e[0]){
      case "sort": case "const": case "nat": case "strlit": r=0;break;
      case "var": r=e[1]+1;break;
      case "app": case "pi": case "lam": children=[e[1],e[2]];break;
      case "proj": children=[e[3]];break;
      case "let": children=[e[1],e[2],e[3]];break;
      default: r=Number.POSITIVE_INFINITY;
    }
    if(children){
      work.push({e,build:true,n:children.length});
      for(let i=children.length-1;i>=0;i--) work.push({e:children[i]});
    }else{k.__looseRangeMemo.set(e,r);vals.push(r);}
  }
  return vals[0];
}

function shiftMap(k,e){
  let m=k.__binderShiftMemo.get(e);
  if(!m){m=new Map();k.__binderShiftMemo.set(e,m);}
  return m;
}
function substMap(k,e,arg){
  let byArg=k.__binderSubstMemo.get(e);
  if(!byArg){byArg=new WeakMap();k.__binderSubstMemo.set(e,byArg);}
  let m=byArg.get(arg);
  if(!m){m=new Map();byArg.set(arg,m);}
  return m;
}

p.run=function(...args){
  this.__binderShiftMemo=new WeakMap();
  this.__binderSubstMemo=new WeakMap();
  this.__looseRangeMemo=new WeakMap();
  this.__binderStats={shiftHits:0,shiftMisses:0,substHits:0,substMisses:0,rangeHits:0,rangeMisses:0,rangeSkips:0};
  return run0.apply(this,args);
};

// Explicit traversal retains the exact cache keys and closed-subtree skips
// without reintroducing host recursion above the stack-safe kernel transforms.
function transport(k,root,operand,start,substitution){
  const work=[{e:root,depth:start}],vals=[];
  const prefix=substitution?"subst":"shift";
  while(work.length){
    const f=work.pop(),e=f.e,d=f.depth;
    if(f.build){
      const xs=vals.splice(vals.length-f.n,f.n);
      const out=e[0]==="proj"?k.make("proj",e[1],e[2],xs[0]):k.make(e[0],...xs);
      f.cache.set(f.key,out);vals.push(out);continue;
    }
    if(!Array.isArray(e)){
      vals.push(substitution?sub0.call(k,e,operand,d):shift0.call(k,e,operand,d));continue;
    }
    const cache=substitution?substMap(k,e,operand):shiftMap(k,e);
    const key=substitution?d:operand+":"+d;
    if(cache.has(key)){k.__binderStats[prefix+"Hits"]++;vals.push(cache.get(key));continue;}
    if(looseRange(k,e)<=d){
      k.__binderStats.rangeSkips++;cache.set(key,e);vals.push(e);continue;
    }
    k.__binderStats[prefix+"Misses"]++;k.tick();
    let out,children;
    switch(e[0]){
      case "sort": case "const": case "nat": case "strlit": out=e;break;
      case "var":
        out=substitution?(e[1]===d?k.shift(operand,d):e[1]>d?k.make("var",e[1]-1):e)
          :(e[1]<d?e:k.make("var",e[1]+operand));break;
      case "pi": case "lam": children=[[e[1],d],[e[2],d+1]];break;
      case "app": children=[[e[1],d],[e[2],d]];break;
      case "proj": children=[[e[3],d]];break;
      case "let": children=[[e[1],d],[e[2],d],[e[3],d+1]];break;
      default:
        // The retained implementation decides unsupported syntax. As before,
        // never publish a cache entry for this fallback or a failed transform.
        vals.push(substitution?sub0.call(k,e,operand,d):shift0.call(k,e,operand,d));continue;
    }
    if(children){
      work.push({e,build:true,n:children.length,cache,key});
      for(let i=children.length-1;i>=0;i--) work.push({e:children[i][0],depth:children[i][1]});
    }else{cache.set(key,out);vals.push(out);}
  }
  return vals[0];
}

p.shift=function(e,amount,cut=0){
  ensure(this);
  if(!Array.isArray(e)) return shift0.call(this,e,amount,cut);
  if(amount===0) return e;
  return transport(this,e,amount,cut,false);
};

p.substitute=function(e,arg,depth=0){
  ensure(this);
  if(!Array.isArray(e)||!Array.isArray(arg)) return sub0.call(this,e,arg,depth);
  return transport(this,e,arg,depth,true);
};
