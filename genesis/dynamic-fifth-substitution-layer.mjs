import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,sub0=p.substitute;

function ensure(k){
  k.__slotSupport??=new WeakMap();
  k.__slotStats??={queries:0,direct:0,unchanged:0,rebuilt:0,supportHits:0,supportStores:0};
}
function support(k,e){
  if(!Array.isArray(e))return 0;
  ensure(k);
  const old=k.__slotSupport.get(e);
  if(old!==undefined){k.__slotStats.supportHits++;return old;}
  k.tick();k.__slotStats.supportStores++;
  let n;
  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":n=0;break;
    case "var":n=e[1]+1;break;
    case "app":n=Math.max(support(k,e[1]),support(k,e[2]));break;
    case "proj":n=support(k,e[3]);break;
    case "pi":case "lam":n=Math.max(support(k,e[1]),Math.max(0,support(k,e[2])-1));break;
    case "let":n=Math.max(support(k,e[1]),support(k,e[2]),Math.max(0,support(k,e[3])-1));break;
    default:return -1;
  }
  k.__slotSupport.set(e,n);return n;
}
function fiveArgConstSpine(root){
  let n=0,h=root;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  return n===5&&Array.isArray(h)&&h[0]==="const";
}

p.run=function(...args){
  this.__slotSupport=new WeakMap();
  this.__slotStats={queries:0,direct:0,unchanged:0,rebuilt:0,supportHits:0,supportStores:0};
  return run0.apply(this,args);
};

p.substitute=function(root,arg,depth=0){
  ensure(this);
  if(depth===0&&Array.isArray(root)&&root[0]==="app"&&fiveArgConstSpine(root)){
    this.__slotStats.queries++;
    // The entire function prefix (head + first four arguments) is closed.
    // Therefore de-Bruijn substitution cannot alter it for any argument.
    if(support(this,root[1])===0){
      this.__slotStats.direct++;
      if(support(this,root[2])===0){this.__slotStats.unchanged++;return root;}
      const dyn=sub0.call(this,root[2],arg,0);
      if(dyn===root[2]){this.__slotStats.unchanged++;return root;}
      this.__slotStats.rebuilt++;
      return this.make("app",root[1],dyn);
    }
  }
  return sub0.call(this,root,arg,depth);
};
