import { Kernel, Stop } from "./kernel-base.mjs";

// Retained execution consequence from the rigid-type-spine separator.
//
// A comparison whose raw applications share one exact rigid inductive head may
// try congruence before normalization/unfolding. The attempt is transactional:
// it has one 250k semantic-step budget, compares cheaper argument pairs first,
// may recurse through exact same-head inner application spines, and on any
// failure restores both semantic budget and conversion frontier before falling
// back to the retained converter.
//
// This adds no definitional equality rule: successful congruence is only a
// sufficient proof of an equality the kernel already recognizes. Local
// definition fallback is deliberately excluded and keeps its verified path.

const retainedEqual = Kernel.prototype.equal;
const SPECULATION_CAP = 250000;

function rawSpine(e) {
  const args=[];
  while(Array.isArray(e) && e[0]==="app") {
    args.push(e[2]);
    e=e[1];
  }
  args.reverse();
  return {head:e,args};
}

function cheapPair(a,b) {
  if(a===b) return -1000000;
  if(!Array.isArray(a)||!Array.isArray(b)) return 0;
  if(a[0]!==b[0]) return -10000;
  if(["const","var","nat","strlit","sort"].includes(a[0])) return -5000;
  let score=0,stack=[a,b],seen=new Set();
  while(stack.length && score<128) {
    const x=stack.pop();
    if(!Array.isArray(x)||seen.has(x)) continue;
    seen.add(x); score++;
    for(let i=1;i<x.length;i++) if(Array.isArray(x[i])) stack.push(x[i]);
  }
  return score;
}

Kernel.prototype.equal = function(a,b,ctx=[]) {
  if(this.localDefs) return retainedEqual.call(this,a,b,ctx);
  if(this.same(a,b)) return;

  const depth=this._rigidTypeSpineDepth??0;
  const sa=rawSpine(a),sb=rawSpine(b);
  const sameHead=sa.args.length>0 && sa.args.length===sb.args.length &&
    (sa.head===sb.head || this.same(sa.head,sb.head));
  const d=sameHead && sa.head?.[0]==="const" ? this.env.get(sa.head[1]) : null;

  // Only a rigid inductive type constructor may start speculation. Once inside
  // that one transaction, congruence may recursively decompose exact same-head
  // application spines of any head kind.
  if(!sameHead || (depth===0 && d?.kind!=="inductive"))
    return retainedEqual.call(this,a,b,ctx);

  const outer=depth===0;
  let snap=null;
  if(outer) {
    snap={steps:this.steps,frontier:this.conversionFrontier,budget:this.budget};
    this.budget=Math.min(this.budget,this.steps+SPECULATION_CAP);
  }

  this._rigidTypeSpineDepth=depth+1;
  const order=sa.args.map((_,i)=>i)
    .sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));

  try {
    for(const i of order) this.equal(sa.args[i],sb.args[i],ctx);
    this._rigidTypeSpineDepth=depth;
    if(outer) this.budget=snap.budget;
    return;
  } catch(e) {
    this._rigidTypeSpineDepth=depth;
    if(!(e instanceof Stop || e instanceof RangeError)) {
      if(outer) this.budget=snap.budget;
      throw e;
    }
    if(outer) {
      this.budget=snap.budget;
      this.steps=snap.steps;
      this.conversionFrontier=snap.frontier;
      return retainedEqual.call(this,a,b,ctx);
    }
    return retainedEqual.call(this,a,b,ctx);
  }
};
