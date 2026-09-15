import { Kernel, Stop } from "./kernel-base.mjs";

// Retained execution consequence from the lazy-delta separator.
//
// The previously verified rigid-inductive congruence remains underneath this
// layer as the fallback. This layer starts one larger transactional comparison
// only at an exact rigid inductive application. Inside that transaction:
//
//   * exact same-head application spines use congruence;
//   * differing heads expose only shallow definitional computation;
//   * a folded definition is exposed before evaluating an already exposed recursor;
//   * when the opposite head is already a recursor, delta unfolding stops before
//     iota so the heads can align at the coarsest sufficient reduction depth.
//
// Any failed speculative comparison restores semantic steps/frontier and falls
// back to the retained converter. No new definitional equality rule is added.

const fallbackEqual = Kernel.prototype.equal;
const SPECULATION_CAP = 650000;

function rawSpine(e) {
  const args=[];
  while(Array.isArray(e) && e[0]==="app") {
    args.push(e[2]);
    e=e[1];
  }
  args.reverse();
  return {head:e,args};
}

function rebuild(kernel,head,args) {
  let out=head;
  for(const a of args) out=kernel.make("app",out,a);
  return out;
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

function headKind(kernel,t) {
  const h=rawSpine(t).head;
  if(!Array.isArray(h)) return null;
  if(h[0]!=="const") return h[0];
  return kernel.env.get(h[1])?.kind??"const";
}

function administrative(kernel,t) {
  let cur=t;
  for(let n=0;n<16;n++) {
    if(!Array.isArray(cur)) return cur;
    if(cur[0]==="let") {
      kernel.tick(); kernel.need("reduction");
      cur=kernel.substitute(cur[3],cur[2]);
      continue;
    }
    const s=rawSpine(cur);
    if(Array.isArray(s.head) && s.head[0]==="lam" && s.args.length) {
      kernel.tick(); kernel.need("reduction");
      cur=rebuild(kernel,kernel.substitute(s.head[2],s.args[0]),s.args.slice(1));
      continue;
    }
    return cur;
  }
  return cur;
}

function unfoldDefOnly(kernel,t) {
  const cur=administrative(kernel,t),s=rawSpine(cur);
  if(!Array.isArray(s.head)||s.head[0]!=="const") return null;
  const d=kernel.env.get(s.head[1]);
  if(d?.kind!=="def") return null;
  kernel.tick(); kernel.need("declarations"); kernel.need("reduction");
  let out=kernel.instantiateDeclaration(s.head,d.value);
  out=administrative(kernel,rebuild(kernel,out,s.args));
  return out;
}

function rawIota(kernel,t) {
  const s=rawSpine(t),rh=s.head,rargs=s.args;
  if(!Array.isArray(rh)||rh[0]!=="const") return null;
  const rd=kernel.env.get(rh[1]);
  if(rd?.kind!=="rec") return null;

  const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
  if(rargs.length<total) return null;

  const ms=rawSpine(rargs[total-1]),mh=ms.head,margs=ms.args;
  const md=Array.isArray(mh)&&mh[0]==="const" ? kernel.env.get(mh[1]) : null;
  if(md?.kind!=="ctor" || md.induct!==rd.induct ||
     margs.length!==md.numParams+md.numFields) return null;

  for(let i=0;i<rd.numParams;i++)
    if(!kernel.same(margs[i],rargs[i])) return null;

  const rule=rd.rules.find(rr=>rr.ctor===md.name);
  if(!rule) return null;

  kernel.need("inductive-reduction"); kernel.need("reduction");
  let rhs=kernel.instantiateDeclaration(rh,rule.rhs);
  rhs=kernel.appN(rhs,
    rargs.slice(0,rd.numParams+1+rd.numMinors).concat(margs.slice(md.numParams)));
  for(const extra of rargs.slice(total)) rhs=kernel.make("app",rhs,extra);
  return administrative(kernel,rhs);
}

function reduceHeadOnce(kernel,t,allowMajor=true) {
  let cur=administrative(kernel,t),s=rawSpine(cur);

  if(Array.isArray(s.head)&&s.head[0]==="const") {
    const d=kernel.env.get(s.head[1]);
    if(d?.kind==="def") {
      kernel.tick(); kernel.need("declarations"); kernel.need("reduction");
      let out=kernel.instantiateDeclaration(s.head,d.value);
      out=administrative(kernel,rebuild(kernel,out,s.args));
      return rawIota(kernel,out)??out;
    }
  }

  const iota=rawIota(kernel,cur);
  if(iota!==null) return iota;

  if(allowMajor) {
    const rs=rawSpine(cur),rh=rs.head,rargs=rs.args;
    if(Array.isArray(rh)&&rh[0]==="const") {
      const rd=kernel.env.get(rh[1]);
      if(rd?.kind==="rec") {
        const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
        if(rargs.length>=total) {
          const major=rargs[total-1];
          const next=reduceHeadOnce(kernel,major,false);
          if(next!==null&&next!==major) {
            const xs=rargs.slice();
            xs[total-1]=next;
            return rebuild(kernel,rh,xs);
          }
        }
      }
    }
  }

  return cur===t ? null : cur;
}

function traceSig(kernel,t) {
  const s=rawSpine(t),h=s.head;
  let head=null,kind=null;
  if(Array.isArray(h)) {
    head=h[0]==="const"?h[1]:h[0];
    kind=h[0]==="const"?(kernel.env.get(h[1])?.kind??"const"):h[0];
  }
  return {head,kind,args:s.args.length,tag:Array.isArray(t)?t[0]:typeof t};
}

Kernel.prototype.equal = function(a,b,ctx=[]) {
  // This execution optimization was acquired after function eta in the retained
  // developmental sequence. Do not let it mask that capability's ablation.
  if(this.localDefs || !this.caps.has("function-eta"))
    return fallbackEqual.call(this,a,b,ctx);

  const depth=this._lazyDeltaDepth??0;
  if(depth>0) this.__lazyDeltaLastPair={steps:this.steps,a:traceSig(this,a),b:traceSig(this,b),ctx:ctx.length};
  if(this.same(a,b)) return;

  const sa=rawSpine(a),sb=rawSpine(b);
  const sameHead=sa.args.length>0 && sa.args.length===sb.args.length &&
    (sa.head===sb.head || this.same(sa.head,sb.head));
  const d=sameHead && Array.isArray(sa.head) && sa.head[0]==="const"
    ? this.env.get(sa.head[1]) : null;

  if(depth===0) {
    if(!sameHead || d?.kind!=="inductive")
      return fallbackEqual.call(this,a,b,ctx);

    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    this.__lazyDeltaTopStarts=(this.__lazyDeltaTopStarts??0)+1;
    this.budget=Math.min(this.budget,this.steps+SPECULATION_CAP);
    this._lazyDeltaDepth=1;
    const order=sa.args.map((_,i)=>i)
      .sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));

    try {
      for(const i of order) this.equal(sa.args[i],sb.args[i],ctx);
      this._lazyDeltaDepth=0;
      this.budget=snap.budget;
      this.__lazyDeltaTopSuccesses=(this.__lazyDeltaTopSuccesses??0)+1;
      this.__lazyDeltaLastSuccess={start:snap.steps,end:this.steps,delta:this.steps-snap.steps};
      return;
    } catch(e) {
      this._lazyDeltaDepth=0;
      this.budget=snap.budget;
      if(!(e instanceof Stop || e instanceof RangeError)) throw e;
      this.__lazyDeltaTopFailures=(this.__lazyDeltaTopFailures??0)+1;
      this.__lazyDeltaLastFailure={start:snap.steps,failedAt:this.steps,delta:this.steps-snap.steps,
        reason:e.message,lastPair:this.__lazyDeltaLastPair??null};
      this.steps=snap.steps;
      this.conversionFrontier=snap.frontier;
      return fallbackEqual.call(this,a,b,ctx);
    }
  }

  if(sameHead) {
    const order=sa.args.map((_,i)=>i)
      .sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
    for(const i of order) this.equal(sa.args[i],sb.args[i],ctx);
    return;
  }

  let x=a,y=b;
  for(let n=0;n<12000;n++) {
    if(this.same(x,y)) return;

    const sx=rawSpine(x),sy=rawSpine(y);
    if(sx.args.length>0 && sx.args.length===sy.args.length &&
       (sx.head===sy.head || this.same(sx.head,sy.head))) {
      const order=sx.args.map((_,i)=>i)
        .sort((i,j)=>cheapPair(sx.args[i],sy.args[i])-cheapPair(sx.args[j],sy.args[j]));
      for(const i of order) this.equal(sx.args[i],sy.args[i],ctx);
      return;
    }

    const kx=headKind(this,x),ky=headKind(this,y);

    // Stop at the first grain where an exposed recursor can align with a folded
    // definition. Do not iota-reduce past that prospective separator.
    if(kx==="rec" && ky==="def") {
      const ny=unfoldDefOnly(this,y);
      if(ny!==null&&ny!==y) { y=ny; continue; }
      const nx=reduceHeadOnce(this,x,true);
      if(nx!==null&&nx!==x) { x=nx; continue; }
    } else if(ky==="rec" && kx==="def") {
      const nx=unfoldDefOnly(this,x);
      if(nx!==null&&nx!==x) { x=nx; continue; }
      const ny=reduceHeadOnce(this,y,true);
      if(ny!==null&&ny!==y) { y=ny; continue; }
    } else if(ky==="def" && kx!=="def") {
      const ny=reduceHeadOnce(this,y,true);
      if(ny!==null&&ny!==y) { y=ny; continue; }
      const nx=reduceHeadOnce(this,x,true);
      if(nx!==null&&nx!==x) { x=nx; continue; }
    } else {
      const nx=reduceHeadOnce(this,x,true);
      if(nx!==null&&nx!==x) { x=nx; continue; }
      const ny=reduceHeadOnce(this,y,true);
      if(ny!==null&&ny!==y) { y=ny; continue; }
    }

    return fallbackEqual.call(this,x,y,ctx);
  }

  return fallbackEqual.call(this,x,y,ctx);
};
