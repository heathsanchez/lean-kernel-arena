import {Kernel} from "./kernel-base.mjs";

// Private WHNF closure machine. It is activated only for substitutions made
// while WHNF is running whose body is a five-argument constant-headed spine,
// the residual family isolated by the shared-subterm census.
//
// Unlike the rejected Proxy experiment, no closure object is ever inserted into
// the kernel AST. The machine either consumes the environment while reducing or
// materializes an ordinary canonical term before returning to retained code.
const p=Kernel.prototype,run0=p.run,whnf0=p.whnf,sub0=p.substitute;
const C=(term,env)=>({term,env});

function ensure(k){
  k.__privateSupport??=new WeakMap();
  k.__privateStats??={queries:0,targetCalls:0,closureSteps:0,beta:0,defs:0,recs:0,
    vars:0,lets:0,materialized:0,reusedClosed:0,reusedNoEnv:0,paramChecks:0,maxEnv:0,maxArgs:0};
}
function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return{h,args};
}
function freeMask(k,root){
  if(!Array.isArray(root))return 0n;
  k.__privateMask??=new WeakMap();
  const old=k.__privateMask.get(root);if(old!==undefined)return old;
  let m;
  switch(root[0]){
    case "sort":case "const":case "nat":case "strlit":m=0n;break;
    case "var":m=1n<<BigInt(root[1]);break;
    case "app":m=freeMask(k,root[1])|freeMask(k,root[2]);break;
    case "proj":m=freeMask(k,root[3]);break;
    case "pi":case "lam":m=freeMask(k,root[1])|(freeMask(k,root[2])>>1n);break;
    case "let":m=freeMask(k,root[1])|freeMask(k,root[2])|(freeMask(k,root[3])>>1n);break;
    default:return null;
  }
  k.__privateMask.set(root,m);return m;
}
function target(k,root){
  if(!Array.isArray(root))return false;
  const s=spine(root);
  if(s.args.length!==5||!Array.isArray(s.h)||s.h[0]!=="const")return false;
  let closed=0,uses0=0;
  for(const a of s.args){
    const m=freeMask(k,a);if(m===null)return false;
    if(m===0n){closed++;continue;}
    if((m&1n)!==0n){uses0++;continue;}
    return false;
  }
  return closed===4&&uses0===1;
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
  const e=cl.term,env=cl.env;ensure(k);
  if(!Array.isArray(e))return e;
  if(env.length===0){k.__privateStats.reusedNoEnv++;return e;}
  const sup=support(k,e);
  if(sup===0){k.__privateStats.reusedClosed++;return e;}
  k.tick();k.__privateStats.materialized++;
  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":return e;
    case "var":{
      const i=e[1];if(i<depth)return e;
      const j=i-depth;
      if(j<env.length){
        let out=materialize(k,env[j],0);
        if(depth!==0&&support(k,out)!==0)out=k.shift(out,depth);
        return out;
      }
      const ni=depth+(j-env.length);return ni===i?e:k.make("var",ni);
    }
    case "pi":case "lam":
      return k.make(e[0],materialize(k,C(e[1],env),depth),materialize(k,C(e[2],env),depth+1));
    case "app":
      return k.make("app",materialize(k,C(e[1],env),depth),materialize(k,C(e[2],env),depth));
    case "proj":
      return k.make("proj",e[1],e[2],materialize(k,C(e[3],env),depth));
    case "let":
      return k.make("let",materialize(k,C(e[1],env),depth),materialize(k,C(e[2],env),depth),
        materialize(k,C(e[3],env),depth+1));
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
  if(a.term===b.term&&a.env===b.env)return true;
  const x=materialize(k,a,0),y=materialize(k,b,0);
  return x!==null&&y!==null&&k.same(x,y);
}
function evalClosure(k,start,args=[],level=0){
  if(level>64)return {head:start,args,stuck:true};
  let cl=start,pending=args.slice();
  for(;;){
    ensure(k);k.tick();k.__privateStats.closureSteps++;
    k.__privateStats.maxEnv=Math.max(k.__privateStats.maxEnv,cl.env.length);
    k.__privateStats.maxArgs=Math.max(k.__privateStats.maxArgs,pending.length);
    const e=cl.term,env=cl.env;
    if(!Array.isArray(e))return {head:cl,args:pending,stuck:true};

    if(e[0]==="app"){pending.unshift(C(e[2],env));cl=C(e[1],env);continue;}
    if(e[0]==="var"){
      if(e[1]<env.length){k.__privateStats.vars++;cl=env[e[1]];continue;}
      return {head:cl,args:pending,stuck:false};
    }
    if(e[0]==="let"){k.need("reduction");k.__privateStats.lets++;cl=C(e[3],[C(e[2],env),...env]);continue;}
    if(e[0]==="lam"&&pending.length){
      k.need("reduction");k.__privateStats.beta++;cl=C(e[2],[pending.shift(),...env]);continue;
    }
    if(e[0]==="nat"){
      // Literal expansion is left to the retained WHNF after materialization;
      // the closure machine adds no new literal semantics.
      return {head:cl,args:pending,stuck:false};
    }
    if(e[0]==="proj"){
      const obj=evalClosure(k,C(e[3],env),[],level+1),mh=obj.head.term,ind=k.env.get(e[1]);
      if(ind?.kind==="inductive"&&ind.ctors?.length===1&&Array.isArray(mh)&&mh[0]==="const"&&mh[1]===ind.ctors[0]){
        const pos=ind.numParams+e[2];if(pos>=obj.args.length)k.reject("projection-out-of-range");
        cl=obj.args[pos];continue;
      }
      const ordinary=materializeState(k,obj);
      if(ordinary===null)return {head:cl,args:pending,stuck:true};
      cl=C(k.make("proj",e[1],e[2],ordinary),[]);return {head:cl,args:pending,stuck:false};
    }
    if(e[0]==="const"){
      k.need("declarations");
      const d=k.env.get(e[1]);if(!d)k.reject("undeclared-constant");
      if(d.kind==="def"){
        k.need("reduction");k.__privateStats.defs++;
        cl=C(k.instantiateDeclaration(e,d.value),[]);continue;
      }
      if(d.kind==="rec"){
        const total=d.numParams+1+d.numMinors+d.numIndices+1;
        if(pending.length>=total){
          const major=evalClosure(k,pending[total-1],[],level+1);
          const mh=major.head.term,md=Array.isArray(mh)&&mh[0]==="const"?k.env.get(mh[1]):null;
          if(md?.kind==="ctor"&&md.induct===d.induct&&major.args.length===md.numParams+md.numFields){
            let ok=true;
            for(let i=0;i<d.numParams;i++)if(!sameClosure(k,major.args[i],pending[i])){ok=false;break;}
            if(ok){
              const rule=d.rules.find(rr=>rr.ctor===md.name);
              if(rule){
                k.need("inductive-reduction");k.need("reduction");k.__privateStats.recs++;
                const prefix=pending.slice(0,d.numParams+1+d.numMinors);
                const fields=major.args.slice(md.numParams),extras=pending.slice(total);
                pending=prefix.concat(fields,extras);
                cl=C(k.instantiateDeclaration(e,rule.rhs),[]);
                continue;
              }
            }
          }
        }
      }
      return {head:cl,args:pending,stuck:false};
    }
    return {head:cl,args:pending,stuck:false};
  }
}
function reduceTarget(k,body,arg){
  const state=evalClosure(k,C(body,[C(arg,[])]));
  const out=materializeState(k,state);
  return out===null?sub0.call(k,body,arg,0):out;
}

p.run=function(...args){
  this.__privateSupport=new WeakMap();
  this.__privateMask=new WeakMap();
  this.__privateStats={queries:0,targetCalls:0,closureSteps:0,beta:0,defs:0,recs:0,
    vars:0,lets:0,materialized:0,reusedClosed:0,reusedNoEnv:0,paramChecks:0,maxEnv:0,maxArgs:0};
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
    if(target(this,root)){
      this.__privateStats.targetCalls++;
      return reduceTarget(this,root,arg);
    }
  }
  return sub0.call(this,root,arg,depth);
};
