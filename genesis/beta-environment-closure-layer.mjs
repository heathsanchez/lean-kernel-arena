import {Kernel} from "./kernel-base.mjs";

// Prospective execution-only separator.
// Multi-beta WHNF uses an explicit de-Bruijn environment instead of repeatedly
// materializing substitute(body,arg). Closures never escape this WHNF request:
// the retained kernel still receives ordinary term arrays at the boundary.
const retainedRun=Kernel.prototype.run;
const retainedWhnf=Kernel.prototype.whnf;

const C=(term,env)=>({term,env});

function support(k,root){
  if(!Array.isArray(root)) return 0;
  k.__betaEnvSupport??=new WeakMap();
  const old=k.__betaEnvSupport.get(root);
  if(old!==undefined){k.__betaEnvStats.supportHits++;return old;}
  k.tick(); k.__betaEnvStats.supportStores++;
  let n;
  switch(root[0]){
    case "sort": case "const": case "nat": case "strlit": n=0; break;
    case "var": n=root[1]+1; break;
    case "app": n=Math.max(support(k,root[1]),support(k,root[2])); break;
    case "proj": n=support(k,root[3]); break;
    case "pi": case "lam": {
      const a=support(k,root[1]),b=support(k,root[2]);
      n=Math.max(a,Math.max(0,b-1)); break;
    }
    case "let": {
      const a=support(k,root[1]),v=support(k,root[2]),b=support(k,root[3]);
      n=Math.max(a,v,Math.max(0,b-1)); break;
    }
    default: return -1;
  }
  k.__betaEnvSupport.set(root,n);
  return n;
}

function materialize(k,cl,depth=0){
  const e=cl.term,env=cl.env;
  if(!Array.isArray(e)) return e;
  if(env.length===0){k.__betaEnvStats.reusedNoEnv++;return e;}
  const sup=support(k,e);
  if(sup===0){k.__betaEnvStats.reusedClosed++;return e;}
  k.tick(); k.__betaEnvStats.materializedVisits++;
  switch(e[0]){
    case "sort": case "const": case "nat": case "strlit": return e;
    case "var": {
      const i=e[1];
      if(i<depth) return e;
      const j=i-depth;
      if(j<env.length){
        k.__betaEnvStats.envLookups++;
        let out=materialize(k,env[j],0);
        if(depth!==0 && support(k,out)!==0) out=k.shift(out,depth);
        return out;
      }
      const ni=depth+(j-env.length);
      return ni===i?e:k.make("var",ni);
    }
    case "pi": case "lam":
      return k.make(e[0],materialize(k,C(e[1],env),depth),
        materialize(k,C(e[2],env),depth+1));
    case "app":
      return k.make("app",materialize(k,C(e[1],env),depth),
        materialize(k,C(e[2],env),depth));
    case "proj":
      return k.make("proj",e[1],e[2],materialize(k,C(e[3],env),depth));
    case "let":
      return k.make("let",materialize(k,C(e[1],env),depth),
        materialize(k,C(e[2],env),depth),
        materialize(k,C(e[3],env),depth+1));
    default:
      k.__betaEnvStats.fallbacks++;
      return null;
  }
}

function flattenRoot(k,e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){
    k.tick(); k.need("application");
    args.push(C(h[2],[])); h=h[1];
  }
  args.reverse();
  return {head:h,args};
}

function closureWhnf(k,root){
  const first=flattenRoot(k,root);
  // Keep the experiment narrow: only application spines whose raw head is a
  // lambda and which contain at least two arguments enter the closure machine.
  if(!Array.isArray(first.head)||first.head[0]!=="lam"||first.args.length<2)
    return null;

  let cl=C(first.head,[]),args=first.args,beta=0;
  for(;;){
    const e=cl.term,env=cl.env;
    if(!Array.isArray(e)) break;
    k.tick();
    if(e[0]==="app"){
      args.unshift(C(e[2],env));
      cl=C(e[1],env);
      continue;
    }
    if(e[0]==="var"&&e[1]<env.length){
      k.__betaEnvStats.envHeadLookups++;
      cl=env[e[1]];
      continue;
    }
    if(e[0]==="let"){
      k.need("reduction");
      cl=C(e[3],[C(e[2],env),...env]);
      k.__betaEnvStats.letEnvExtensions++;
      continue;
    }
    if(e[0]==="lam"&&args.length){
      k.need("reduction");
      cl=C(e[2],[args.shift(),...env]);
      beta++;k.__betaEnvStats.betaReductions++;
      continue;
    }
    break;
  }
  if(beta<2) return null;

  let out=materialize(k,cl,0);
  if(out===null) return null;
  for(const a of args){
    const ma=materialize(k,a,0);
    if(ma===null) return null;
    out=k.make("app",out,ma);
  }
  k.__betaEnvStats.closureSpines++;
  return out;
}

export function installBetaEnvironmentClosures(enabled=true){
  Kernel.prototype.run=retainedRun;
  Kernel.prototype.whnf=retainedWhnf;
  if(!enabled) return;

  Kernel.prototype.run=function(...args){
    this.__betaEnvSupport=new WeakMap();
    this.__betaEnvStats={closureSpines:0,betaReductions:0,envHeadLookups:0,envLookups:0,
      letEnvExtensions:0,materializedVisits:0,reusedClosed:0,reusedNoEnv:0,
      supportHits:0,supportStores:0,fallbacks:0};
    return retainedRun.apply(this,args);
  };

  Kernel.prototype.whnf=function(e){
    this.__betaEnvStats??={closureSpines:0,betaReductions:0,envHeadLookups:0,envLookups:0,
      letEnvExtensions:0,materializedVisits:0,reusedClosed:0,reusedNoEnv:0,
      supportHits:0,supportStores:0,fallbacks:0};
    if(this.localDefs===true||this.__betaEnvBypass||!Array.isArray(e)||e[0]!=="app")
      return retainedWhnf.call(this,e);
    let out;
    try{out=closureWhnf(this,e);}
    catch(err){throw err;}
    if(out===null) return retainedWhnf.call(this,e);
    this.__betaEnvBypass=true;
    try{return retainedWhnf.call(this,out);}
    finally{this.__betaEnvBypass=false;}
  };
}
