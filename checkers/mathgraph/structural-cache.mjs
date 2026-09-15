import { Kernel } from "./kernel-base.mjs";

// Exact memoization for the two pure de-Bruijn tree transforms that dominate
// the retained execution residual. The transforms are also evaluated with
// explicit work stacks, so stack safety does not discard the previously earned
// per-subtree reuse. Keys remain exact: expression/argument object identity
// plus every numeric parameter. Only successful completed results are cached.
//
// An exact cache hit is a compiled successful consequence: the identical
// transform has already been verified and paid for in this run, so reuse does
// not repay semantic work. This mirrors the retained normalization cache.
const oldRun = Kernel.prototype.run;

Kernel.prototype.run = function(...args) {
  this._shiftCache = new WeakMap();
  this._substCache = new WeakMap();
  return oldRun.apply(this,args);
};

function shiftMap(kernel,e) {
  let m=kernel._shiftCache?.get(e);
  if(!m) {
    m=new Map();
    kernel._shiftCache?.set(e,m);
  }
  return m;
}
function substMap(kernel,e,arg) {
  let byExpr=kernel._substCache?.get(e);
  if(!byExpr) {
    byExpr=new WeakMap();
    kernel._substCache?.set(e,byExpr);
  }
  let byDepth=byExpr.get(arg);
  if(!byDepth) {
    byDepth=new Map();
    byExpr.set(arg,byDepth);
  }
  return byDepth;
}

Kernel.prototype.shift = function(root,amount,cut=0) {
  const work=[{kind:"visit",e:root,cut}], vals=[];
  while(work.length) {
    const f=work.pop();
    if(f.kind==="build") {
      let out;
      if(f.tag==="proj") {
        out=this.make("proj",f.name,f.index,vals.pop());
      } else {
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
        out=this.make(f.tag,...xs);
      }
      shiftMap(this,f.e).set(f.key,out);
      vals.push(out);
      continue;
    }

    const e=f.e,c=f.cut,key=`${amount}:${c}`,cache=shiftMap(this,e);
    if(cache.has(key)) {
      vals.push(cache.get(key));
      continue;
    }

    this.tick();
    let out;
    switch(e[0]) {
      case "sort": case "const": case "nat": case "strlit":
        out=e; cache.set(key,out); vals.push(out); break;
      case "var":
        out=e[1]<c ? e : this.make("var",e[1]+amount);
        cache.set(key,out); vals.push(out); break;
      case "pi": case "lam":
        work.push({kind:"build",tag:e[0],n:2,e,key});
        work.push({kind:"visit",e:e[2],cut:c+1});
        work.push({kind:"visit",e:e[1],cut:c});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2,e,key});
        work.push({kind:"visit",e:e[2],cut:c});
        work.push({kind:"visit",e:e[1],cut:c});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2],e,key});
        work.push({kind:"visit",e:e[3],cut:c});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3,e,key});
        work.push({kind:"visit",e:e[3],cut:c+1});
        work.push({kind:"visit",e:e[2],cut:c});
        work.push({kind:"visit",e:e[1],cut:c});
        break;
      default: this.unknown("shift-syntax");
    }
  }
  return vals.pop();
};

Kernel.prototype.substitute = function(root,arg,depth=0) {
  const work=[{kind:"visit",e:root,depth}], vals=[];
  while(work.length) {
    const f=work.pop();
    if(f.kind==="build") {
      let out;
      if(f.tag==="proj") {
        out=this.make("proj",f.name,f.index,vals.pop());
      } else {
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
        out=this.make(f.tag,...xs);
      }
      substMap(this,f.e,arg).set(f.depth,out);
      vals.push(out);
      continue;
    }

    const e=f.e,d=f.depth,cache=substMap(this,e,arg);
    if(cache.has(d)) {
      vals.push(cache.get(d));
      continue;
    }

    this.tick();
    let out;
    switch(e[0]) {
      case "sort": case "const": case "nat": case "strlit":
        out=e; cache.set(d,out); vals.push(out); break;
      case "var":
        out=e[1]===d ? this.shift(arg,d) : e[1]>d ? this.make("var",e[1]-1) : e;
        cache.set(d,out); vals.push(out); break;
      case "pi": case "lam":
        work.push({kind:"build",tag:e[0],n:2,e,depth:d});
        work.push({kind:"visit",e:e[2],depth:d+1});
        work.push({kind:"visit",e:e[1],depth:d});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2,e,depth:d});
        work.push({kind:"visit",e:e[2],depth:d});
        work.push({kind:"visit",e:e[1],depth:d});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2],e,depth:d});
        work.push({kind:"visit",e:e[3],depth:d});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3,e,depth:d});
        work.push({kind:"visit",e:e[3],depth:d+1});
        work.push({kind:"visit",e:e[2],depth:d});
        work.push({kind:"visit",e:e[1],depth:d});
        break;
      default: this.unknown("substitution-syntax");
    }
  }
  return vals.pop();
};
