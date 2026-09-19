import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,shift0=p.shift,sub0=p.substitute;

function ensure(k){
  k.__binderShiftMemo??=new WeakMap();
  k.__binderSubstMemo??=new WeakMap();
  k.__looseRangeMemo??=new WeakMap();
  k.__binderStats??={shiftHits:0,shiftMisses:0,substHits:0,substMisses:0,rangeHits:0,rangeMisses:0,rangeSkips:0};
  k.__substKeyDiag??={total:0,newExpression:0,newArgument:0,newDepth:0,exactRepeat:0,seen:new WeakMap(),argFamilySampled:0,argFamilies:new Map()};
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
  this.__substKeyDiag={total:0,newExpression:0,newArgument:0,newDepth:0,exactRepeat:0,seen:new WeakMap(),argFamilySampled:0,argFamilies:new Map()};
  return run0.apply(this,args);
};

const ARG_FAMILY_SAMPLE_LIMIT=100_000;

function appFamily(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();
  let head;
  if(Array.isArray(h)&&h[0]==="const")head=["const",h[1]];
  else if(Array.isArray(h))head=[h[0]];
  else head=[typeof h];
  const argTags=args.map(x=>Array.isArray(x)?x[0]:typeof x);
  return ["app",head,args.length,argTags];
}
function argFamily(e){
  if(!Array.isArray(e))return [typeof e];
  switch(e[0]){
    case "app": return appFamily(e);
    case "const": return ["const",e[1]];
    case "var": return ["var"];
    case "nat": return ["nat"];
    case "strlit": return ["strlit"];
    case "pi": case "lam":
      return [e[0],Array.isArray(e[1])?e[1][0]:typeof e[1],Array.isArray(e[2])?e[2][0]:typeof e[2]];
    case "let":
      return ["let",...e.slice(1).map(x=>Array.isArray(x)?x[0]:typeof x)];
    case "proj":
      return ["proj",String(e[1]),String(e[2]),Array.isArray(e[3])?e[3][0]:typeof e[3]];
    default: return [String(e[0]??"<unknown>")];
  }
}

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
    if(substitution){
      ensure(k);
      const q=k.__substKeyDiag;
      q.total++;
      let byArg=q.seen.get(e);
      if(!byArg){
        q.newExpression++;
        byArg=new WeakMap();
        q.seen.set(e,byArg);
        byArg.set(operand,new Set([d]));
      }else{
        let depths=byArg.get(operand);
        if(!depths){
          q.newArgument++;
          if(q.argFamilySampled<ARG_FAMILY_SAMPLE_LIMIT){
            q.argFamilySampled++;
            const family=JSON.stringify(argFamily(operand));
            q.argFamilies.set(family,(q.argFamilies.get(family)??0)+1);
          }
          depths=new Set([d]);
          byArg.set(operand,depths);
        }else if(!depths.has(d)){
          q.newDepth++;
          depths.add(d);
        }else{
          q.exactRepeat++;
        }
      }
    }
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
