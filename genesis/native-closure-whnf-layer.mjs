import {Kernel} from "./kernel-base.mjs";
import {makeClosure,nativeWhnf,reifyClosure} from "./native-closure-whnf.mjs";

// Experimental evaluator-only integration.
//
// Closures exist only while reducing a WHNF segment.  The public Kernel.whnf
// boundary still returns ordinary immutable expression arrays, so infer/equal,
// declarations and all retained conversion machinery remain unchanged.
// Unsupported heads delegate to the already-qualified retained evaluator.
const p=Kernel.prototype;
const retainedWhnf=p.whnf;

function stats(k){
  return k.__nativeClosureStats??={calls:0,beta:0,let:0,delta:0,fallback:0,
    bypassLocalDefs:0,materializations:0};
}

function appSpine(e){
  const args=[];let head=e;
  while(Array.isArray(head)&&head[0]==="app"){
    args.push(head[2]);
    head=head[1];
  }
  args.reverse();
  return {head,args};
}

function rebuild(k,head,args){
  let out=head;
  for(const arg of args) out=k.make("app",out,arg);
  return out;
}

function syntacticClosureWork(e){
  if(!Array.isArray(e)) return null;
  if(e[0]==="let") return {beta:0,let:1};
  if(e[0]!=="app") return null;
  const {head,args}=appSpine(e);
  if(head?.[0]!=="lam"||args.length===0) return null;
  let beta=0,letCount=0,cur=head,n=args.length;
  // Count only reductions that are guaranteed from the visible head spine.
  while(n>0&&Array.isArray(cur)&&cur[0]==="lam"){
    beta++;n--;cur=cur[2];
    while(Array.isArray(cur)&&cur[0]==="let") {letCount++;cur=cur[3];}
  }
  return {beta,let:letCount};
}

function nativeSegment(k,e,s){
  const visible=syntacticClosureWork(e);
  if(visible===null) return null;
  const out=nativeWhnf(makeClosure(e));
  s.beta+=visible.beta;
  s.let+=visible.let;
  s.materializations++;
  return reifyClosure(out);
}

function definitionSegment(k,e,s){
  if(!Array.isArray(e)||e[0]!=="app") return null;
  const {head,args}=appSpine(e);
  if(head?.[0]!=="const") return null;
  const d=k.env?.get(head[1]);
  if(d?.kind!=="def") return null;
  k.need("declarations");
  k.need("reduction");
  // Universe instantiation remains owned by the retained kernel.  Only the
  // resulting ordinary body enters the transient closure evaluator.
  const body=k.instantiateDeclaration(head,d.value);
  const expanded=rebuild(k,body,args);
  const visible=syntacticClosureWork(expanded);
  if(visible===null) return null;
  s.delta++;
  const out=nativeWhnf(makeClosure(expanded));
  s.beta+=visible.beta;
  s.let+=visible.let;
  s.materializations++;
  return reifyClosure(out);
}

function delegate(k,e,s,kind="fallback"){
  if(kind==="fallback") s.fallback++;
  else s.bypassLocalDefs++;
  const prior=k.__nativeClosureDelegate;
  k.__nativeClosureDelegate=true;
  try{return retainedWhnf.call(k,e);}
  finally{k.__nativeClosureDelegate=prior;}
}

export function installNativeClosureWhnf(enabled=true){
  p.whnf=retainedWhnf;
  if(!enabled) return;
  p.whnf=function(e){
    const s=stats(this);s.calls++;
    if(this.__nativeClosureDelegate===true) return retainedWhnf.call(this,e);
    if(this.localDefs===true) return delegate(this,e,s,"localDefs");

    let out=nativeSegment(this,e,s);
    if(out===null) out=definitionSegment(this,e,s);
    if(out===null) return delegate(this,e,s);

    // The closure firewall: materialize to ordinary syntax before re-entering
    // retained WHNF.  Further unsupported Lean rules remain authoritative there.
    const prior=this.__nativeClosureDelegate;
    this.__nativeClosureDelegate=true;
    try{return retainedWhnf.call(this,out);}
    finally{this.__nativeClosureDelegate=prior;}
  };
}
