import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,sub0=p.substitute;

function mask(k,e){
  if(!Array.isArray(e))return 0n;
  k.__fvMask??=new WeakMap();
  if(k.__fvMask.has(e)){k.__fvStats.maskHits++;return k.__fvMask.get(e);}
  k.tick();k.__fvStats.maskStores++;
  let m;
  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":m=0n;break;
    case "var":m=1n<<BigInt(e[1]);break;
    case "pi":case "lam":
      m=mask(k,e[1])|(mask(k,e[2])>>1n);break;
    case "app":
      m=mask(k,e[1])|mask(k,e[2]);break;
    case "proj":
      m=mask(k,e[3]);break;
    case "let":
      m=mask(k,e[1])|mask(k,e[2])|(mask(k,e[3])>>1n);break;
    default:return null;
  }
  k.__fvMask.set(e,m);return m;
}

function subst(k,e,arg,depth){
  const m=mask(k,e);
  if(m===null)return sub0.call(k,e,arg,depth);
  const d=BigInt(depth),target=1n<<d;
  if((m&target)===0n && (m>>(d+1n))===0n){
    k.tick();
    k.__fvStats.skipped++;
    return e;
  }
  k.tick();k.__fvStats.visited++;
  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":return e;
    case "var":
      if(e[1]===depth)return k.shift(arg,depth);
      return e[1]>depth?k.make("var",e[1]-1):e;
    case "pi":case "lam":
      return k.make(e[0],subst(k,e[1],arg,depth),subst(k,e[2],arg,depth+1));
    case "app":
      return k.make("app",subst(k,e[1],arg,depth),subst(k,e[2],arg,depth));
    case "proj":
      return k.make("proj",e[1],e[2],subst(k,e[3],arg,depth));
    case "let":
      return k.make("let",subst(k,e[1],arg,depth),subst(k,e[2],arg,depth),subst(k,e[3],arg,depth+1));
    default:return sub0.call(k,e,arg,depth);
  }
}

p.run=function(...args){
  this.__fvMask=new WeakMap();
  this.__fvStats={maskHits:0,maskStores:0,skipped:0,visited:0,queries:0};
  return run0.apply(this,args);
};
p.substitute=function(e,arg,depth=0){
  this.__fvStats??={maskHits:0,maskStores:0,skipped:0,visited:0,queries:0};
  this.__fvStats.queries++;
  return subst(this,e,arg,depth);
};
