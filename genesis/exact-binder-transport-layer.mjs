import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,shift0=p.shift,sub0=p.substitute;

function ensure(k){
  k.__binderShiftMemo??=new WeakMap();
  k.__binderSubstMemo??=new WeakMap();
  k.__looseRangeMemo??=new WeakMap();
  k.__binderStats??={shiftHits:0,shiftMisses:0,substHits:0,substMisses:0,rangeHits:0,rangeMisses:0,rangeSkips:0};
}

function looseRange(k,e){
  if(!Array.isArray(e)) return Number.POSITIVE_INFINITY;
  const hit=k.__looseRangeMemo.get(e);
  if(hit!==undefined){k.__binderStats.rangeHits++;return hit;}
  k.__binderStats.rangeMisses++;
  let r;
  switch(e[0]){
    case "sort": case "const": case "nat": case "strlit": r=0; break;
    case "var": r=e[1]+1; break;
    case "app": r=Math.max(looseRange(k,e[1]),looseRange(k,e[2])); break;
    case "proj": r=looseRange(k,e[3]); break;
    case "pi": case "lam":
      r=Math.max(looseRange(k,e[1]),Math.max(0,looseRange(k,e[2])-1)); break;
    case "let":
      r=Math.max(looseRange(k,e[1]),looseRange(k,e[2]),Math.max(0,looseRange(k,e[3])-1)); break;
    default: r=Number.POSITIVE_INFINITY;
  }
  k.__looseRangeMemo.set(e,r);
  return r;
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

p.shift=function(e,amount,cut=0){
  ensure(this);
  if(!Array.isArray(e)) return shift0.call(this,e,amount,cut);
  if(amount===0) return e;
  const key=amount+":"+cut,m=shiftMap(this,e);
  if(m.has(key)){this.__binderStats.shiftHits++;return m.get(key);}
  const range=looseRange(this,e);
  if(range<=cut){
    this.__binderStats.rangeSkips++;
    m.set(key,e);
    return e;
  }
  this.__binderStats.shiftMisses++;
  this.tick();
  let out;
  switch(e[0]){
    case "sort": case "const": case "nat": case "strlit": out=e; break;
    case "var": out=e[1]<cut?e:this.make("var",e[1]+amount); break;
    case "pi": case "lam": out=this.make(e[0],this.shift(e[1],amount,cut),this.shift(e[2],amount,cut+1)); break;
    case "app": out=this.make("app",this.shift(e[1],amount,cut),this.shift(e[2],amount,cut)); break;
    case "proj": out=this.make("proj",e[1],e[2],this.shift(e[3],amount,cut)); break;
    case "let": out=this.make("let",this.shift(e[1],amount,cut),this.shift(e[2],amount,cut),this.shift(e[3],amount,cut+1)); break;
    default: return shift0.call(this,e,amount,cut);
  }
  m.set(key,out);
  return out;
};

p.substitute=function(e,arg,depth=0){
  ensure(this);
  if(!Array.isArray(e)||!Array.isArray(arg)) return sub0.call(this,e,arg,depth);
  const m=substMap(this,e,arg);
  if(m.has(depth)){this.__binderStats.substHits++;return m.get(depth);}
  const range=looseRange(this,e);
  if(range<=depth){
    this.__binderStats.rangeSkips++;
    m.set(depth,e);
    return e;
  }
  this.__binderStats.substMisses++;
  this.tick();
  let out;
  switch(e[0]){
    case "sort": case "const": case "nat": case "strlit": out=e; break;
    case "var":
      out=e[1]===depth?this.shift(arg,depth):e[1]>depth?this.make("var",e[1]-1):e; break;
    case "pi": case "lam":
      out=this.make(e[0],this.substitute(e[1],arg,depth),this.substitute(e[2],arg,depth+1)); break;
    case "app":
      out=this.make("app",this.substitute(e[1],arg,depth),this.substitute(e[2],arg,depth)); break;
    case "proj":
      out=this.make("proj",e[1],e[2],this.substitute(e[3],arg,depth)); break;
    case "let":
      out=this.make("let",this.substitute(e[1],arg,depth),this.substitute(e[2],arg,depth),this.substitute(e[3],arg,depth+1)); break;
    default: return sub0.call(this,e,arg,depth);
  }
  m.set(depth,out);
  return out;
};
