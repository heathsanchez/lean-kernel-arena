import {Kernel} from "./kernel-base.mjs";

// Exact targeted closure for the residual discovered by the shared beta census:
// an application spine with a closed head, five arguments, four closed branches,
// and exactly one branch depending on the substituted binder.
//
// Only that dynamic branch receives a transparent pending de-Bruijn substitution.
// No global shift/substitute semantics change; every other call is retained.
const p=Kernel.prototype,run0=p.run,sub0=p.substitute;
const META=Symbol("dynamic-slot-closure");

function ensure(k){
  k.__dynamicMask??=new WeakMap();
  k.__dynamicClosures??=new WeakMap();
  k.__dynamicIds??=new WeakMap();k.__dynamicNextId??=1;
  k.__dynamicStats??={queries:0,targetCalls:0,lazySlots:0,closures:0,closureHits:0,
    forcedNodes:0,maskHits:0,maskStores:0,reusedClosed:0};
}
function oid(k,x){
  if(!Array.isArray(x))return "p:"+String(x);
  let id=k.__dynamicIds.get(x);if(id===undefined){id=k.__dynamicNextId++;k.__dynamicIds.set(x,id);}return id;
}
function freeMask(k,root){
  ensure(k);
  if(!Array.isArray(root))return 0n;
  if(k.__dynamicMask.has(root)){k.__dynamicStats.maskHits++;return k.__dynamicMask.get(root);}
  k.tick();k.__dynamicStats.maskStores++;
  let m;
  switch(root[0]){
    case "sort":case "const":case "nat":case "strlit":m=0n;break;
    case "var":m=1n<<BigInt(root[1]);break;
    case "app":m=freeMask(k,root[1])|freeMask(k,root[2]);break;
    case "proj":m=freeMask(k,root[3]);break;
    case "pi":case "lam":m=freeMask(k,root[1])|(freeMask(k,root[2])>>1n);break;
    case "let":m=freeMask(k,root[1])|freeMask(k,root[2])|(freeMask(k,root[3])>>1n);break;
    default:m=-1n;
  }
  k.__dynamicMask.set(root,m);return m;
}
function adjusted(op,underBinder){
  if(!underBinder)return op;
  if(op.kind==="shift")return {kind:"shift",amount:op.amount,cut:op.cut+1};
  return {kind:"subst",arg:op.arg,depth:op.depth+1};
}
function opKey(k,ops){
  return ops.map(op=>op.kind==="shift"?"s:"+op.amount+":"+op.cut:"u:"+oid(k,op.arg)+":"+op.depth).join("|");
}
function lazy(k,base,ops){
  ensure(k);
  if(!Array.isArray(base)||ops.length===0)return base;
  if(base[META]!==undefined){const q=base[META];base=q.base;ops=q.ops.concat(ops);}
  let byOps=k.__dynamicClosures.get(base);
  if(!byOps){byOps=new Map();k.__dynamicClosures.set(base,byOps);}
  const key=opKey(k,ops),old=byOps.get(key);
  if(old!==undefined){k.__dynamicStats.closureHits++;return old;}
  k.tick();k.__dynamicStats.closures++;
  const meta={kernel:k,base,ops,view:null,proxy:null};
  const proxy=new Proxy([],{
    get(_t,prop){
      if(prop===META)return meta;
      const v=force(meta),out=v[prop];
      return typeof out==="function"?out.bind(v):out;
    }
  });
  meta.proxy=proxy;byOps.set(key,proxy);return proxy;
}
function force(meta){
  if(meta.view!==null)return meta.view;
  const k=meta.kernel,base=meta.base,ops=meta.ops;ensure(k);
  k.__dynamicStats.forcedNodes++;
  if(!Array.isArray(base)){meta.view=base;return base;}

  if(base[0]==="var"){
    let i=base[1];
    for(let oi=0;oi<ops.length;oi++){
      const op=ops[oi];k.tick();
      if(op.kind==="shift"){if(i>=op.cut)i+=op.amount;continue;}
      if(i===op.depth){
        const tail=[];
        if(op.depth!==0)tail.push({kind:"shift",amount:op.depth,cut:0});
        for(let j=oi+1;j<ops.length;j++)tail.push(ops[j]);
        const q=lazy(k,op.arg,tail);
        meta.view=q[META]!==undefined?force(q[META]):q;return meta.view;
      }
      if(i>op.depth)i--;
    }
    meta.view=i===base[1]?base:k.make("var",i);return meta.view;
  }

  for(let i=0;i<ops.length;i++)k.tick();
  switch(base[0]){
    case "sort":case "const":case "nat":case "strlit":meta.view=base;return base;
    case "pi":case "lam":
      meta.view=k.make(base[0],lazy(k,base[1],ops),lazy(k,base[2],ops.map(op=>adjusted(op,true))));
      return meta.view;
    case "app":
      meta.view=k.make("app",lazy(k,base[1],ops),lazy(k,base[2],ops));return meta.view;
    case "proj":
      meta.view=k.make("proj",base[1],base[2],lazy(k,base[3],ops));return meta.view;
    case "let":
      meta.view=k.make("let",lazy(k,base[1],ops),lazy(k,base[2],ops),
        lazy(k,base[3],ops.map(op=>adjusted(op,true))));return meta.view;
    default:
      // This cannot occur for validated kernel syntax; preserve the retained
      // frontier rather than inventing a transformation.
      return sub0.call(k,base,["sort",0],0);
  }
}
function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return{h,args};
}
function target(k,root){
  const {h,args}=spine(root);
  if(args.length!==5||freeMask(k,h)!==0n)return null;
  let dynamic=-1,closed=0;
  for(let i=0;i<args.length;i++){
    const m=freeMask(k,args[i]);
    if(m===0n){closed++;continue;}
    if((m&1n)!==0n && dynamic===-1){dynamic=i;continue;}
    return null;
  }
  return closed===4&&dynamic!==-1?{h,args,dynamic}:null;
}

p.run=function(...args){
  this.__dynamicMask=new WeakMap();this.__dynamicClosures=new WeakMap();
  this.__dynamicIds=new WeakMap();this.__dynamicNextId=1;
  this.__dynamicStats={queries:0,targetCalls:0,lazySlots:0,closures:0,closureHits:0,
    forcedNodes:0,maskHits:0,maskStores:0,reusedClosed:0};
  return run0.apply(this,args);
};

p.substitute=function(root,arg,depth=0){
  ensure(this);
  if(depth!==0||!Array.isArray(root))return sub0.call(this,root,arg,depth);
  this.__dynamicStats.queries++;
  const t=target(this,root);
  if(t===null)return sub0.call(this,root,arg,depth);
  this.__dynamicStats.targetCalls++;
  let out=t.h;
  for(let i=0;i<t.args.length;i++){
    let a;
    if(i===t.dynamic){
      a=lazy(this,t.args[i],[{kind:"subst",arg,depth:0}]);
      this.__dynamicStats.lazySlots++;
    }else{
      a=t.args[i];this.__dynamicStats.reusedClosed++;
    }
    out=this.make("app",out,a);
  }
  return out;
};
