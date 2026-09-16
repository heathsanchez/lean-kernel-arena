import {Kernel} from "./kernel-base.mjs";

// Private WHNF closure machine for the measured five-argument substitution
// residual. Closures never enter the kernel AST. Exact closure/evaluation/
// materialization consequences are interned and memoized within one kernel run.
const p=Kernel.prototype,run0=p.run,whnf0=p.whnf,sub0=p.substitute;
const EMPTY_ENV=Object.freeze([]);

function ensure(k){
  k.__privateSupport??=new WeakMap();
  k.__privateClosures??=new WeakMap();
  k.__privateEnvCons??=new WeakMap();
  k.__privateMaterialize??=new WeakMap();
  k.__privateEval??=new WeakMap();
  k.__privateState??=new Map();
  k.__privateClosureIds??=new WeakMap();k.__privateClosureNext??=1;
  k.__privateStats??={queries:0,targetCalls:0,closureSteps:0,beta:0,defs:0,recs:0,
    vars:0,lets:0,materialized:0,reusedClosed:0,reusedNoEnv:0,paramChecks:0,
    maxEnv:0,maxArgs:0,closureHits:0,envHits:0,materializeHits:0,
    materializeStores:0,evalHits:0,evalStores:0,stateHits:0,stateStores:0};
}

function C(k,term,env=EMPTY_ENV){
  ensure(k);
  if(!env?.length)env=EMPTY_ENV;
  if(!Array.isArray(term))return {term,env};
  let byEnv=k.__privateClosures.get(term);
  if(!(byEnv instanceof WeakMap)){byEnv=new WeakMap();k.__privateClosures.set(term,byEnv);}
  let old=byEnv.get(env);
  if(old!==undefined){k.__privateStats.closureHits++;return old;}
  const out={term,env};byEnv.set(env,out);return out;
}

function extend(k,item,parent){
  ensure(k);
  let byItem=k.__privateEnvCons.get(parent);
  if(!(byItem instanceof WeakMap)){byItem=new WeakMap();k.__privateEnvCons.set(parent,byItem);}
  let old=byItem.get(item);
  if(old!==undefined){k.__privateStats.envHits++;return old;}
  const out=Object.freeze([item,...parent]);byItem.set(item,out);return out;
}

function slot(root,term,env){
  if(!Array.isArray(term)||!env||typeof env!=="object")return null;
  let byEnv=root.get(term);
  if(!(byEnv instanceof WeakMap)){byEnv=new WeakMap();root.set(term,byEnv);}
  return {has:()=>byEnv.has(env),get:()=>byEnv.get(env),set:v=>byEnv.set(env,v)};
}

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return{h,args};
}
function target(root){
  if(!Array.isArray(root))return false;
  const s=spine(root);
  return s.args.length===5&&Array.isArray(s.h)&&s.h[0]==="const";
}

function support(k,e){
  if(!Array.isArray(e))return 0;
  ensure(k);
  const old=k.__privateSupport.get(e);if(old!==undefined)return old;
  k.tick();
  let n;
  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":n=0;break;
    case "var":n=e[1]+1;break;
    case "app":n=Math.max(support(k,e[1]),support(k,e[2]));break;
    case "proj":n=support(k,e[3]);break;
    case "pi":case "lam":n=Math.max(support(k,e[1]),Math.max(0,support(k,e[2])-1));break;
    case "let":n=Math.max(support(k,e[1]),support(k,e[2]),Math.max(0,support(k,e[3])-1));break;
    default:n=-1;
  }
  k.__privateSupport.set(e,n);return n;
}

function materialize(k,cl,depth=0){
  ensure(k);
  const e=cl.term,env=cl.env;
  if(!Array.isArray(e))return e;
  if(env.length===0){k.__privateStats.reusedNoEnv++;return e;}

  let cache=null;
  if(depth===0){
    cache=slot(k.__privateMaterialize,e,env);
    if(cache?.has()){k.__privateStats.materializeHits++;return cache.get();}
  }
  const save=out=>{
    if(cache&&out!==null){cache.set(out);k.__privateStats.materializeStores++;}
    return out;
  };

  const sup=support(k,e);
  if(sup===0){k.__privateStats.reusedClosed++;return save(e);}
  k.tick();k.__privateStats.materialized++;

  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":return save(e);
    case "var":{
      const i=e[1];
      if(i<depth)return save(e);
      const j=i-depth;
      if(j<env.length){
        let out=materialize(k,env[j],0);
        if(depth!==0&&support(k,out)!==0)out=k.shift(out,depth);
        return save(out);
      }
      const ni=depth+(j-env.length);
      return save(ni===i?e:k.make("var",ni));
    }
    case "pi":case "lam":
      return save(k.make(e[0],
        materialize(k,C(k,e[1],env),depth),
        materialize(k,C(k,e[2],env),depth+1)));
    case "app":
      return save(k.make("app",
        materialize(k,C(k,e[1],env),depth),
        materialize(k,C(k,e[2],env),depth)));
    case "proj":
      return save(k.make("proj",e[1],e[2],materialize(k,C(k,e[3],env),depth)));
    case "let":
      return save(k.make("let",
        materialize(k,C(k,e[1],env),depth),
        materialize(k,C(k,e[2],env),depth),
        materialize(k,C(k,e[3],env),depth+1)));
    default:return null;
  }
}

function materializeState(k,state){
  let out=materialize(k,state.head,0);
  if(out===null)return null;
  for(const a of state.args){
    const x=materialize(k,a,0);if(x===null)return null;
    out=k.make("app",out,x);
  }
  return out;
}

function sameClosure(k,a,b){
  k.__privateStats.paramChecks++;
  if(a===b||(a.term===b.term&&a.env===b.env))return true;
  const x=materialize(k,a,0),y=materialize(k,b,0);
  return x!==null&&y!==null&&k.same(x,y);
}

function closureId(k,cl){
  let id=k.__privateClosureIds.get(cl);
  if(id!==undefined)return id;
  id=k.__privateClosureNext++;k.__privateClosureIds.set(cl,id);return id;
}
function stateKey(k,cl,pending){
  let s=String(closureId(k,cl));
  for(const a of pending)s+=","+closureId(k,a);
  return s;
}
function storeStatePath(k,path,out){
  if(out.stuck)return;
  const saved={head:out.head,args:Object.freeze(out.args.slice()),stuck:false};
  for(const key of path)if(!k.__privateState.has(key)){
    k.__privateState.set(key,saved);k.__privateStats.stateStores++;
  }
}
function evalClosure(k,start,args=[],level=0){
  ensure(k);
  const cacheable=args.length===0&&Array.isArray(start.term);
  const cache=cacheable?slot(k.__privateEval,start.term,start.env):null;
  if(cache?.has()){k.__privateStats.evalHits++;return cache.get();}
  const out=evalClosureUncached(k,start,args,level);
  if(cache&&!out.stuck){
    const saved={head:out.head,args:Object.freeze(out.args.slice()),stuck:false};
    cache.set(saved);k.__privateStats.evalStores++;return saved;
  }
  return out;
}

function evalClosureUncached(k,start,args=[],level=0){
  if(level>64)return {head:start,args,stuck:true};
  let cl=start,pending=args.slice(),statePath=[];
  const finish=out=>{storeStatePath(k,statePath,out);return out;};
  for(;;){
    ensure(k);
    const sk=stateKey(k,cl,pending),prior=k.__privateState.get(sk);
    if(prior!==undefined){
      k.__privateStats.stateHits++;
      storeStatePath(k,statePath,prior);
      return prior;
    }
    statePath.push(sk);
    k.tick();k.__privateStats.closureSteps++;
    k.__privateStats.maxEnv=Math.max(k.__privateStats.maxEnv,cl.env.length);
    k.__privateStats.maxArgs=Math.max(k.__privateStats.maxArgs,pending.length);
    const e=cl.term,env=cl.env;
    if(!Array.isArray(e))return finish({head:cl,args:pending,stuck:true});

    if(e[0]==="app"){
      pending.unshift(C(k,e[2],env));cl=C(k,e[1],env);continue;
    }
    if(e[0]==="var"){
      if(e[1]<env.length){k.__privateStats.vars++;cl=env[e[1]];continue;}
      return finish({head:cl,args:pending,stuck:false});
    }
    if(e[0]==="let"){
      k.need("reduction");k.__privateStats.lets++;
      cl=C(k,e[3],extend(k,C(k,e[2],env),env));continue;
    }
    if(e[0]==="lam"&&pending.length){
      k.need("reduction");k.__privateStats.beta++;
      cl=C(k,e[2],extend(k,pending.shift(),env));continue;
    }
    if(e[0]==="nat")
      return finish({head:cl,args:pending,stuck:false});

    if(e[0]==="proj"){
      const obj=evalClosure(k,C(k,e[3],env),[],level+1);
      const mh=obj.head.term,ind=k.env.get(e[1]);
      if(ind?.kind==="inductive"&&ind.ctors?.length===1&&
         Array.isArray(mh)&&mh[0]==="const"&&mh[1]===ind.ctors[0]){
        const pos=ind.numParams+e[2];
        if(pos>=obj.args.length)k.reject("projection-out-of-range");
        cl=obj.args[pos];continue;
      }
      const ordinary=materializeState(k,obj);
      if(ordinary===null)return finish({head:cl,args:pending,stuck:true});
      cl=C(k,k.make("proj",e[1],e[2],ordinary),EMPTY_ENV);
      return finish({head:cl,args:pending,stuck:false});
    }

    if(e[0]==="const"){
      k.need("declarations");
      const d=k.env.get(e[1]);if(!d)k.reject("undeclared-constant");
      if(d.kind==="def"){
        k.need("reduction");k.__privateStats.defs++;
        cl=C(k,k.instantiateDeclaration(e,d.value),EMPTY_ENV);continue;
      }
      if(d.kind==="rec"){
        const total=d.numParams+1+d.numMinors+d.numIndices+1;
        if(pending.length>=total){
          const major=evalClosure(k,pending[total-1],[],level+1);
          const mh=major.head.term;
          const md=Array.isArray(mh)&&mh[0]==="const"?k.env.get(mh[1]):null;
          if(md?.kind==="ctor"&&md.induct===d.induct&&
             major.args.length===md.numParams+md.numFields){
            let ok=true;
            for(let i=0;i<d.numParams;i++)
              if(!sameClosure(k,major.args[i],pending[i])){ok=false;break;}
            if(ok){
              const rule=d.rules.find(rr=>rr.ctor===md.name);
              if(rule){
                k.need("inductive-reduction");k.need("reduction");k.__privateStats.recs++;
                const prefix=pending.slice(0,d.numParams+1+d.numMinors);
                const fields=major.args.slice(md.numParams),extras=pending.slice(total);
                pending=prefix.concat(fields,extras);
                cl=C(k,k.instantiateDeclaration(e,rule.rhs),EMPTY_ENV);
                continue;
              }
            }
          }
        }
      }
      return finish({head:cl,args:pending,stuck:false});
    }
    return finish({head:cl,args:pending,stuck:false});
  }
}

function reduceTarget(k,body,arg){
  const env=extend(k,C(k,arg,EMPTY_ENV),EMPTY_ENV);
  const state=evalClosure(k,C(k,body,env));
  const out=materializeState(k,state);
  return out===null?sub0.call(k,body,arg,0):out;
}

p.run=function(...args){
  this.__privateSupport=new WeakMap();
  this.__privateClosures=new WeakMap();
  this.__privateEnvCons=new WeakMap();
  this.__privateMaterialize=new WeakMap();
  this.__privateEval=new WeakMap();
  this.__privateState=new Map();
  this.__privateClosureIds=new WeakMap();this.__privateClosureNext=1;
  this.__privateStats={queries:0,targetCalls:0,closureSteps:0,beta:0,defs:0,recs:0,
    vars:0,lets:0,materialized:0,reusedClosed:0,reusedNoEnv:0,paramChecks:0,
    maxEnv:0,maxArgs:0,closureHits:0,envHits:0,materializeHits:0,
    materializeStores:0,evalHits:0,evalStores:0,stateHits:0,stateStores:0};
  this.__privateWhnfDepth=0;
  return run0.apply(this,args);
};

p.whnf=function(e){
  this.__privateWhnfDepth=(this.__privateWhnfDepth??0)+1;
  try{return whnf0.call(this,e);}
  finally{this.__privateWhnfDepth--;}
};

p.substitute=function(root,arg,depth=0){
  ensure(this);
  if(depth===0&&(this.__privateWhnfDepth??0)>0){
    this.__privateStats.queries++;
    if(target(root)){
      this.__privateStats.targetCalls++;
      return reduceTarget(this,root,arg);
    }
  }
  return sub0.call(this,root,arg,depth);
};
