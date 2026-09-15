import { Kernel } from "./kernel-base.mjs";

// Stack safety is an execution property, not a new semantic capability.
// Replace only structurally recursive traversals with explicit work stacks.
// The retained caches and hash-consing wrap these methods afterwards.

const baseValidate = Kernel.prototype.validate;
const baseWhnf = Kernel.prototype.whnf;
const baseInfer = Kernel.prototype.infer;

Kernel.prototype.validate = function(root) {
  const work=[root];
  while(work.length) {
    const e=work.pop();
    // Leaf validation includes universe traversal and all exact malformed checks.
    if(Array.isArray(e) && ["sort","var","const","nat","strlit"].includes(e[0])) {
      baseValidate.call(this,e);
      continue;
    }
    this.tick();
    if(!Array.isArray(e) || typeof e[0]!=="string") this.reject("malformed-term");
    const arities={sort:2,var:2,const:2,nat:2,strlit:2,proj:4,pi:3,lam:3,app:3,let:4};
    if(!(e[0] in arities)) this.unknown("syntax:"+e[0]);
    if(e.length!==arities[e[0]] && !(e[0]==="const"&&e.length===3)) this.reject("malformed-arity");
    if(e[0]==="proj") {
      this.need("projections");
      if(typeof e[1]!=="string"||!Number.isSafeInteger(e[2])||e[2]<0) this.reject("malformed-projection");
      work.push(e[3]);
      continue;
    }
    // Only composite terms reach here.
    for(let i=e.length-1;i>=1;i--) work.push(e[i]);
  }
};

Kernel.prototype.shift = function(root,amount,cut=0) {
  const work=[{kind:"visit",e:root,cut}], vals=[];
  while(work.length) {
    const f=work.pop();
    if(f.kind==="build") {
      if(f.tag==="proj") {
        const x=vals.pop();
        vals.push(this.make("proj",f.name,f.index,x));
      } else {
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
        vals.push(this.make(f.tag,...xs));
      }
      continue;
    }
    const e=f.e,c=f.cut;
    this.tick();
    switch(e[0]) {
      case "sort": case "const": case "nat": case "strlit":
        vals.push(e); break;
      case "var":
        vals.push(e[1]<c ? e : this.make("var",e[1]+amount)); break;
      case "pi": case "lam":
        work.push({kind:"build",tag:e[0],n:2});
        work.push({kind:"visit",e:e[2],cut:c+1});
        work.push({kind:"visit",e:e[1],cut:c});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2});
        work.push({kind:"visit",e:e[2],cut:c});
        work.push({kind:"visit",e:e[1],cut:c});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2]});
        work.push({kind:"visit",e:e[3],cut:c});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3});
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
      if(f.tag==="proj") {
        const x=vals.pop();
        vals.push(this.make("proj",f.name,f.index,x));
      } else {
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
        vals.push(this.make(f.tag,...xs));
      }
      continue;
    }
    const e=f.e,d=f.depth;
    this.tick();
    switch(e[0]) {
      case "sort": case "const": case "nat": case "strlit":
        vals.push(e); break;
      case "var":
        vals.push(e[1]===d ? this.shift(arg,d) : e[1]>d ? this.make("var",e[1]-1) : e);
        break;
      case "pi": case "lam":
        work.push({kind:"build",tag:e[0],n:2});
        work.push({kind:"visit",e:e[2],depth:d+1});
        work.push({kind:"visit",e:e[1],depth:d});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2});
        work.push({kind:"visit",e:e[2],depth:d});
        work.push({kind:"visit",e:e[1],depth:d});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2]});
        work.push({kind:"visit",e:e[3],depth:d});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3});
        work.push({kind:"visit",e:e[3],depth:d+1});
        work.push({kind:"visit",e:e[2],depth:d});
        work.push({kind:"visit",e:e[1],depth:d});
        break;
      default: this.unknown("substitution-syntax");
    }
  }
  return vals.pop();
};

Kernel.prototype.same = function(a,b) {
  const work=[[a,b]];
  while(work.length) {
    const [x,y]=work.pop();
    this.tick();
    if(x===y) continue;
    if(!Array.isArray(x)||!Array.isArray(y)||x.length!==y.length) return false;
    for(let i=0;i<x.length;i++) {
      const xa=Array.isArray(x[i]),ya=Array.isArray(y[i]);
      if(xa||ya) {
        if(!xa||!ya) return false;
        work.push([x[i],y[i]]);
      } else if(x[i]!==y[i]) return false;
    }
  }
  return true;
};

// Avoid host recursion on long let chains and ordinary application spines.
// Recursor/quotient heads keep the retained reducer, because those rules inspect
// the complete application before reducing the function position.
Kernel.prototype.whnf = function(e) {
  if(Array.isArray(e) && e[0]==="let") {
    let cur=e;
    while(Array.isArray(cur) && cur[0]==="let") {
      this.tick();
      this.need("reduction");
      cur=this.substitute(cur[3],cur[2]);
    }
    return this.whnf(cur);
  }

  if(Array.isArray(e) && e[0]==="app") {
    const args=[]; let head=e;
    while(Array.isArray(head) && head[0]==="app") {
      args.push(head[2]);
      head=head[1];
    }
    if(args.length>=64) {
      const d=head?.[0]==="const" ? this.env?.get(head[1]) : null;
      if(d?.kind!=="rec" && d?.kind!=="quot") {
        // Match the retained reducer's per-application entry cost.
        for(let i=0;i<args.length;i++) {
          this.tick();
          this.need("application");
        }
        args.reverse();
        let f=this.whnf(head), i=0;
        while(i<args.length && Array.isArray(f) && f[0]==="lam") {
          this.need("reduction");
          f=this.whnf(this.substitute(f[2],args[i++]));
        }
        if(i===args.length) return f;

        let out=f;
        for(;i<args.length;i++) out=this.make("app",out,args[i]);
        const fd=Array.isArray(f)&&f[0]==="const" ? this.env?.get(f[1]) : null;
        if(fd?.kind==="rec" || fd?.kind==="quot") return baseWhnf.call(this,out);
        return out;
      }
    }
  }
  return baseWhnf.call(this,e);
};

Kernel.prototype.normal = function(root) {
  const work=[{kind:"visit",e:root}], vals=[];
  while(work.length) {
    const f=work.pop();
    if(f.kind==="build") {
      if(f.tag==="proj") {
        const x=vals.pop();
        vals.push(this.make("proj",f.name,f.index,x));
      } else {
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
        vals.push(this.make(f.tag,...xs));
      }
      continue;
    }
    this.tick();
    const e=this.whnf(f.e);
    if(["sort","var","const","nat","strlit"].includes(e[0])) {
      vals.push(e);
    } else if(e[0]==="proj") {
      work.push({kind:"build",tag:"proj",name:e[1],index:e[2]});
      work.push({kind:"visit",e:e[3]});
    } else {
      work.push({kind:"build",tag:e[0],n:e.length-1});
      for(let i=e.length-1;i>=1;i--) work.push({kind:"visit",e:e[i]});
    }
  }
  return vals.pop();
};

// Eliminate recursive execution depth on the three binder/application spines.
// Non-spine cases remain byte-for-byte on the retained inference path.
Kernel.prototype.infer = function(e,ctx) {
  if(Array.isArray(e) && e[0]==="app") {
    const args=[]; let head=e;
    while(Array.isArray(head) && head[0]==="app") {
      this.tick();
      this.need("application");
      args.push(head[2]);
      head=head[1];
    }
    args.reverse();
    let ty=this.infer(head,ctx);
    for(const arg of args) {
      const f=this.whnf(ty);
      if(f[0]!=="pi") this.reject("not-a-function");
      this.equal(this.infer(arg,ctx),f[1],ctx);
      ty=this.substitute(f[2],arg);
    }
    return ty;
  }

  if(Array.isArray(e) && e[0]==="lam") {
    const domains=[]; let cur=e, cctx=ctx;
    while(Array.isArray(cur) && cur[0]==="lam") {
      this.tick();
      this.need("binders");
      this.sortOf(cur[1],cctx);
      domains.push(cur[1]);
      cctx=[...cctx,cur[1]];
      cur=cur[2];
    }
    let ty=this.infer(cur,cctx);
    for(let i=domains.length-1;i>=0;i--) ty=this.make("pi",domains[i],ty);
    return ty;
  }

  if(Array.isArray(e) && e[0]==="pi") {
    const levels=[]; let cur=e, cctx=ctx;
    while(Array.isArray(cur) && cur[0]==="pi") {
      this.tick();
      this.need("binders");
      const a=this.sortOf(cur[1],cctx);
      levels.push(a);
      cctx=[...cctx,cur[1]];
      cur=cur[2];
    }
    let b=this.sortOf(cur,cctx), out=null;
    for(let i=levels.length-1;i>=0;i--) {
      const a=levels[i];
      const u=(typeof a==="number"&&typeof b==="number")
        ? (b===0?0:Math.max(a,b))
        : ["imax",a,b];
      out=this.make("sort",u);
      if(i>0) b=this.whnf(out)[1];
    }
    return out;
  }

  if(Array.isArray(e) && e[0]==="let") {
    let cur=e;
    while(Array.isArray(cur) && cur[0]==="let") {
      this.tick();
      this.need("reduction");
      this.sortOf(cur[1],ctx);
      this.equal(this.infer(cur[2],ctx),cur[1],ctx);
      cur=this.substitute(cur[3],cur[2]);
    }
    return this.infer(cur,ctx);
  }

  return baseInfer.call(this,e,ctx);
};
