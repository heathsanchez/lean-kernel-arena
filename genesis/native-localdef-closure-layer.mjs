import {Kernel} from "./kernel-base.mjs";
import {makeClosure,nativeWhnf,reifyClosure} from "./native-closure-whnf.mjs";

// RealityGraph-directed bounded representation expansion.
//
// The giant residual fingerprint independently recurs in two workloads as
// local-definition fallback WHNF calls with exactly 3 or 4 application
// arguments.  This layer compiles only that recurrent interface.  All other
// arities, unsupported heads, non-local-definition kernels, inference,
// equality, declarations, recursors and stored syntax remain on the retained
// implementation.
//
// Closures are transient.  The retained kernel sees an ordinary expression at
// the boundary, and any exposed local definition is resumed with the exact
// LocalDefKernel shift rule before retained WHNF continues.
const p=Kernel.prototype;
const retainedWhnf=p.whnf;

function freshStats(){
  return {calls:0,selected3:0,selected4:0,beta:0,let:0,delta:0,
    materializations:0,resumedLocalDefs:0,delegatedNonLocal:0,
    delegatedNonRecurrent:0,delegatedUnsupported:0};
}
function stats(k){return k.__nativeLocalDefClosureStats??=freshStats();}

function spine(e){
  const args=[];let head=e;
  while(Array.isArray(head)&&head[0]==="app"){
    args.push(head[2]);head=head[1];
  }
  args.reverse();return {head,args};
}
function rebuild(k,head,args){
  let out=head;
  for(const a of args)out=k.make("app",out,a);
  return out;
}

function guaranteedWork(e,nargs){
  let beta=0,letCount=0,cur=e,n=nargs;
  while(n>0&&Array.isArray(cur)&&cur[0]==="lam"){
    beta++;n--;cur=cur[2];
    while(Array.isArray(cur)&&cur[0]==="let"){
      letCount++;cur=cur[3];
    }
  }
  return {beta,let:letCount};
}

function resumeExposedLocalDef(k,term,s){
  // Exact retained consequence from LocalDefKernel.whnf / reentry repair:
  // resolve a local-definition variable at the exposed head, shift its value by
  // index+1, then retain the same application arguments.
  let cur=term;
  for(let guard=0;guard<64;guard++){
    const sp=spine(cur),h=sp.head,ctx=k._activeCtx??[];
    if(!Array.isArray(h)||h[0]!=="var"||h[1]>=ctx.length)return cur;
    const entry=ctx[ctx.length-1-h[1]];
    if(entry?.__localDef!==true)return cur;
    k.tick();k.need("reduction");
    s.resumedLocalDefs++;
    cur=rebuild(k,k.shift(entry.value,h[1]+1),sp.args);
  }
  return cur;
}

function selectedSegment(k,root,s){
  const sp=spine(root),n=sp.args.length;
  if(n!==3&&n!==4)return null;

  let expanded=root,head=sp.head;
  if(Array.isArray(head)&&head[0]==="const"){
    const d=k.env?.get(head[1]);
    if(d?.kind!=="def")return undefined;
    k.need("declarations");k.need("reduction");
    const body=k.instantiateDeclaration(head,d.value);
    expanded=rebuild(k,body,sp.args);
    head=body;
    s.delta++;
  }else if(!Array.isArray(head)||head[0]!=="lam"){
    return undefined;
  }

  // Only enter the closure machine when the visible selected spine is known to
  // perform beta/let work.  Neutral/reducible cases stay retained.
  const w=guaranteedWork(head,n);
  if(w.beta===0)return undefined;

  const out=nativeWhnf(makeClosure(expanded));
  s.beta+=w.beta;s.let+=w.let;s.materializations++;
  if(n===3)s.selected3++;else s.selected4++;
  return resumeExposedLocalDef(k,reifyClosure(out),s);
}

function delegate(k,e,s,kind){
  s[kind]++;
  const old=k.__nativeLocalDefClosureDelegate;
  k.__nativeLocalDefClosureDelegate=true;
  try{return retainedWhnf.call(k,e);}
  finally{k.__nativeLocalDefClosureDelegate=old;}
}

export function installNativeLocalDefClosure(enabled=true){
  p.whnf=retainedWhnf;
  if(!enabled)return;
  p.whnf=function(e){
    const s=stats(this);s.calls++;
    if(this.__nativeLocalDefClosureDelegate===true)return retainedWhnf.call(this,e);
    if(this.localDefs!==true)return delegate(this,e,s,"delegatedNonLocal");
    if(!Array.isArray(e)||e[0]!=="app")return delegate(this,e,s,"delegatedNonRecurrent");

    const arity=spine(e).args.length;
    if(arity!==3&&arity!==4)return delegate(this,e,s,"delegatedNonRecurrent");

    const out=selectedSegment(this,e,s);
    if(out===undefined)return delegate(this,e,s,"delegatedUnsupported");
    if(out===null)return delegate(this,e,s,"delegatedNonRecurrent");

    // Firewall: after one recurrent closure segment, ordinary retained WHNF is
    // authoritative for every remaining Lean rule.
    const old=this.__nativeLocalDefClosureDelegate;
    this.__nativeLocalDefClosureDelegate=true;
    try{return retainedWhnf.call(this,out);}
    finally{this.__nativeLocalDefClosureDelegate=old;}
  };
}
