import { Kernel, Stop, REJECT } from "./kernel-base.mjs";

// Retained execution consequence: allow one definitive constructor-field REJECT
// to escape an already-rigid inductive type-spine comparison.
//
// Why this is narrower than the discarded constructor-ordering experiments:
// - the outer raw terms must already be applications of the exact same installed
//   inductive type constructor;
// - the nested argument pair must be fully-applied occurrences of the exact same
//   constructor of a non-Prop inductive;
// - constructor parameters must be syntactically identical;
// - each data field receives the same bounded retained-conversion slice;
// - only a definitive retained REJECT is propagated;
// - UNKNOWN / host-stack exhaustion remain inconclusive and fall back unchanged.
//
// This introduces no new equality or inequality law. It only exposes a retained
// negative consequence that constructor injectivity already justifies, before
// eager normalization of unrelated constructor fields.
const retainedEqual = Kernel.prototype.equal;
const FIELD_QUANTUM = 1_000;

function spine(e) {
  const args=[];
  while(Array.isArray(e) && e[0]==="app") {
    args.push(e[2]);
    e=e[1];
  }
  args.reverse();
  return {head:e,args};
}

function sameHead(kernel,a,b) {
  return a===b || (Array.isArray(a) && Array.isArray(b) && kernel.same(a,b));
}

function probeNonPropConstructor(kernel,a,b,ctx,originalBudget) {
  const sa=spine(a),sb=spine(b);
  if(sa.args.length===0 || sa.args.length!==sb.args.length ||
     !sameHead(kernel,sa.head,sb.head) || sa.head?.[0]!=="const")
    return null;

  const ctor=kernel.env.get(sa.head[1]);
  if(ctor?.kind!=="ctor") return null;
  const ind=kernel.env.get(ctor.induct);
  if(ind?.kind!=="inductive" || ind.isProp===true) return null;

  const nP=ctor.numParams??0,nF=ctor.numFields??0;
  if(nF<1 || sa.args.length!==nP+nF) return null;
  for(let i=0;i<nP;i++)
    if(!kernel.same(sa.args[i],sb.args[i])) return null;

  let allEqual=true;
  for(let i=nP;i<nP+nF;i++) {
    if(sa.args[i]===sb.args[i] || kernel.same(sa.args[i],sb.args[i])) continue;

    const oldFrontier=kernel.conversionFrontier;
    kernel.budget=Math.min(originalBudget,kernel.steps+FIELD_QUANTUM);
    kernel._rigidCtorRejectDepth=(kernel._rigidCtorRejectDepth??0)+1;
    try {
      retainedEqual.call(kernel,sa.args[i],sb.args[i],ctx);
    } catch(e) {
      if(e instanceof Stop && e.status===REJECT) return {reject:e};
      if(!(e instanceof Stop || e instanceof RangeError)) throw e;
      allEqual=false;
      kernel.conversionFrontier=oldFrontier;
    } finally {
      kernel._rigidCtorRejectDepth--;
      kernel.budget=originalBudget;
    }
  }
  return allEqual ? {equal:true} : {unknown:true};
}

Kernel.prototype.equal = function(a,b,ctx=[]) {
  if(this._rigidCtorRejectDepth) return retainedEqual.call(this,a,b,ctx);
  if(a===b) return;

  const sa=spine(a),sb=spine(b);
  const same=sa.args.length>0 && sa.args.length===sb.args.length &&
    sameHead(this,sa.head,sb.head);
  const outer=same && sa.head?.[0]==="const" ? this.env.get(sa.head[1]) : null;
  if(!same || outer?.kind!=="inductive")
    return retainedEqual.call(this,a,b,ctx);

  const originalBudget=this.budget;
  try {
    for(let i=0;i<sa.args.length;i++) {
      if(sa.args[i]===sb.args[i] || this.same(sa.args[i],sb.args[i])) continue;
      const p=probeNonPropConstructor(this,sa.args[i],sb.args[i],ctx,originalBudget);
      if(p?.reject) throw p.reject;
    }
  } finally {
    this.budget=originalBudget;
  }
  return retainedEqual.call(this,a,b,ctx);
};
