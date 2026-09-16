import { Kernel } from "./kernel-base.mjs";

// Stack safety is an execution property, not a new semantic capability.
// Replace only structurally recursive traversals with explicit work stacks.
// The retained caches and hash-consing wrap these methods afterwards.

const baseValidate = Kernel.prototype.validate;
const baseWhnf = Kernel.prototype.whnf;
const baseInfer = Kernel.prototype.infer;

function stackLevelSub(kernel,u,sub) {
  kernel.tick();
  if(typeof u==="number") return u;
  if(u[0]==="param") return sub.has(u[1])?sub.get(u[1]):u;
  return [u[0],...u.slice(1).map(x=>stackLevelSub(kernel,x,sub))];
}

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

// A slower but fully iterative head evaluator used only after the retained
// checker has actually demonstrated a host-stack obstruction.
function fullStackWhnf(term) {
  const originalTerm=term;
  let cur=term,args=[],dirty=false;

  const absorbApps=t=>{
    const fresh=[];
    while(Array.isArray(t) && t[0]==="app") {
      this.tick();
      this.need("application");
      fresh.push(t[2]);
      t=t[1];
    }
    fresh.reverse();
    if(fresh.length) args=fresh.concat(args);
    return t;
  };
  const rebuild=()=>{
    if(!dirty && cur===originalTerm) return originalTerm;
    if(!dirty && Array.isArray(originalTerm) && originalTerm[0]==="app") return originalTerm;
    let out=cur;
    for(const arg of args) out=this.make("app",out,arg);
    return out;
  };

  cur=absorbApps(cur);
  while(true) {
    if(!Array.isArray(cur)) return cur;

    if(cur[0]==="let") {
      this.tick();
      this.need("reduction");
      cur=this.substitute(cur[3],cur[2]);
      dirty=true;
      cur=absorbApps(cur);
      continue;
    }

    if(cur[0]==="const") {
      this.tick();
      this.need("declarations");
      const d=this.env.get(cur[1]);
      if(!d) this.reject("undeclared-constant");
      if(d.kind==="def") {
        this.need("reduction");
        cur=this.instantiateDeclaration(cur,d.value);
        dirty=true;
        cur=absorbApps(cur);
        continue;
      }
      if(args.length && (d.kind==="rec" || d.kind==="quot")) {
        let out;
        if(!dirty && Array.isArray(originalTerm) && originalTerm[0]==="app") out=originalTerm;
        else {
          out=cur;
          for(const arg of args) out=this.make("app",out,arg);
        }
        return baseWhnf.call(this,out);
      }
      if(!args.length) return cur;
      return rebuild();
    }

    if(cur[0]==="lam") {
      this.tick();
      if(args.length) {
        this.need("reduction");
        const arg=args.shift();
        cur=this.substitute(cur[2],arg);
        dirty=true;
        cur=absorbApps(cur);
        continue;
      }
      return cur;
    }

    if(cur[0]==="nat" || cur[0]==="proj") {
      const reduced=baseWhnf.call(this,cur);
      if(reduced!==cur) {
        cur=reduced;
        dirty=true;
        cur=absorbApps(cur);
        continue;
      }
      if(!args.length) return cur;
      return rebuild();
    }

    // Rigid neutral head: account for the head whnf call. If the initial
    // application was unchanged, return it by identity and avoid reconstruction.
    this.tick();
    if(!args.length) return cur;
    return rebuild();
  }
}

// Exact multi-beta execution compilation.
//
// A raw chain
//   (fun x1 => (fun x2 => ... (fun xn => body) an ...) a2) a1
// is beta-reduced by carrying all substitutions in one positional environment,
// materializing the final body once, then reducing that result on an explicit
// application/recursor/projection continuation. This changes only execution
// order; all reduction cases below are the same retained rules used by baseWhnf.
function collectMultiBeta(root) {
  const args=[];
  let cur=root;
  while(Array.isArray(cur) && cur[0]==="app" &&
        Array.isArray(cur[1]) && cur[1][0]==="lam") {
    args.push(cur[2]);
    cur=cur[1][2];
  }
  return {body:cur,args};
}

function materializeMultiBeta(kernel,body,args) {
  const work=[{kind:"visit",term:body,capture:args.length,depth:0,extra:0}],vals=[];
  while(work.length) {
    const f=work.pop();
    if(f.kind==="build") {
      if(f.tag==="proj") {
        vals.push(kernel.make("proj",f.name,f.index,vals.pop()));
      } else {
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
        vals.push(kernel.make(f.tag,...xs));
      }
      continue;
    }

    const e=f.term;
    kernel.tick();
    switch(e[0]) {
      case "sort": case "const": case "nat": case "strlit":
        vals.push(e); break;
      case "var": {
        const i=e[1];
        if(i<f.depth) {
          vals.push(e);
          break;
        }
        const j=i-f.depth;
        if(j<f.capture) {
          const argIndex=f.capture-1-j;
          work.push({kind:"visit",term:args[argIndex],capture:argIndex,depth:0,extra:f.extra+f.depth});
        } else {
          const ni=f.depth+(j-f.capture)+f.extra;
          vals.push(ni===i?e:kernel.make("var",ni));
        }
        break;
      }
      case "pi": case "lam":
        work.push({kind:"build",tag:e[0],n:2});
        work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth+1,extra:f.extra});
        work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2});
        work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth,extra:f.extra});
        work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2]});
        work.push({kind:"visit",term:e[3],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3});
        work.push({kind:"visit",term:e[3],capture:f.capture,depth:f.depth+1,extra:f.extra});
        work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth,extra:f.extra});
        work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      default:
        kernel.unknown("multi-beta-materialize-syntax");
    }
  }
  return vals.pop();
}

function multiBetaSpineWhnf(kernel,root) {
  const frames=[];

  const rebuild=(head,args)=>{
    let out=head;
    for(const a of args) out=kernel.make("app",out,a);
    return out;
  };

  const flatten=term=>{
    const args=[];
    let head=term;
    while(Array.isArray(head) && head[0]==="app") {
      kernel.tick();
      kernel.need("application");
      args.push(head[2]);
      head=head[1];
    }
    args.reverse();
    return {head,args};
  };

  const attach=(term,extraArgs)=>{
    const st=flatten(term);
    if(extraArgs?.length) st.args.push(...extraArgs);
    return st;
  };

  const resumeRec=(fr,major)=>{
    const {head:rh,args:rargs,d:rd,total}=fr;
    if(major?.[0]==="nat")major=kernel.natLitToConstructor(major);
    else {
      const unfolded=kernel.unfoldTheoremHead(major,"major");
      if(unfolded!==null){
        const unfolds=(fr.majorUnfolds??0)+1;
        if(unfolds>10000)kernel.unknown("theorem-major-unfold-budget");
        frames.push({...fr,majorUnfolds:unfolds});
        return {state:attach(unfolded,[])};
      }
    }
    const ms=flatten(major),mh=ms.head,margs=ms.args;
    const md=mh?.[0]==="const"?kernel.env.get(mh[1]):null;

    if(md?.kind==="ctor" && md.induct===rd.induct &&
       margs.length===md.numParams+md.numFields) {
      let paramsMatch=true;
      for(let i=0;i<rd.numParams;i++) {
        if(!kernel.same(margs[i],rargs[i])) { paramsMatch=false; break; }
      }
      if(paramsMatch) {
        const rule=rd.rules.find(rr=>rr.ctor===md.name);
        if(rule) {
          kernel.need("inductive-reduction");
          kernel.need("reduction");
          const rhs=kernel.instantiateDeclaration(rh,rule.rhs);
          const prefix=rargs.slice(0,rd.numParams+1+rd.numMinors);
          const nextArgs=prefix.concat(margs.slice(md.numParams),rargs.slice(total));
          return {state:attach(rhs,nextArgs)};
        }
      }
    }
    const neutralRhs=kernel.recursorRhsWithoutConstructor(rh,rargs,rd,total);
    if(neutralRhs!==null)return {state:attach(neutralRhs,[])};
    return {value:rebuild(rh,rargs)};
  };

  let state=flatten(root);
  for(;;) {
    let {head,args}=state;

    if(!Array.isArray(head)) return rebuild(head,args);

    if(head[0]==="let") {
      kernel.tick();
      kernel.need("reduction");
      state=attach(kernel.substitute(head[3],head[2]),args);
      continue;
    }

    if(head[0]==="nat") {
      kernel.tick();kernel.need("nat-literals");
    }

    if(head[0]==="lam") {
      kernel.tick();
      if(args.length) {
        kernel.need("reduction");
        state=attach(kernel.substitute(head[2],args[0]),args.slice(1));
        continue;
      }
    }

    if(head[0]==="proj") {
      frames.push({kind:"proj",name:head[1],index:head[2],object:head[3],args});
      state=flatten(head[3]);
      continue;
    }

    if(head[0]==="const") {
      kernel.tick();
      kernel.need("declarations");
      const d=kernel.env.get(head[1]);
      if(!d) kernel.reject("undeclared-constant");

      if(d.kind==="def") {
        kernel.need("reduction");
        state=attach(kernel.instantiateDeclaration(head,d.value),args);
        continue;
      }

      if(d.kind==="rec") {
        const total=d.numParams+1+d.numMinors+d.numIndices+1;
        if(args.length>=total) {
          frames.push({kind:"rec",head,args,d,total});
          state=flatten(args[total-1]);
          continue;
        }
      }
      const quotientMajor=kernel.quotientMajorIndex(head,args);
      if(quotientMajor!==null) {
        frames.push({kind:"quot",head,args});
        state=flatten(args[quotientMajor]);
        continue;
      }
    }

    let result=rebuild(head,args);
    while(frames.length) {
      const fr=frames.pop();

      if(fr.kind==="proj") {
        const ms=flatten(result),mh=ms.head,margs=ms.args;
        const ind=kernel.env.get(fr.name);
        const ctor=ind?.kind==="inductive" && ind.ctors?.length===1 ? ind.ctors[0] : null;
        if(ctor!==null && mh?.[0]==="const" && mh[1]===ctor) {
          const pos=ind.numParams+fr.index;
          if(pos>=margs.length) kernel.reject("projection-out-of-range");
          state=attach(margs[pos],fr.args);
          result=null;
          break;
        }
        const p=result===fr.object
          ? kernel.make("proj",fr.name,fr.index,fr.object)
          : kernel.make("proj",fr.name,fr.index,result);
        result=rebuild(p,fr.args);
        continue;
      }

      if(fr.kind==="quot") {
        const rhs=kernel.quotientRhs(fr.head,fr.args,result);
        if(rhs!==null) {
          state=attach(rhs.head,rhs.args);
          result=null;
          break;
        }
        result=rebuild(fr.head,fr.args);
        continue;
      }

      const resumed=resumeRec(fr,result);
      if(resumed.state) {
        state=resumed.state;
        result=null;
        break;
      }
      result=resumed.value;
    }
    if(result!==null) return result;
  }
}

// Avoid host recursion on long let chains and ordinary application spines.
// Recursor/quotient heads keep the retained reducer, because those rules inspect
// the complete application before reducing the function position.
Kernel.prototype.whnf = function(e) {
  if(this._fullStackSafe===true) return fullStackWhnf.call(this,e);

  if(Array.isArray(e) && e[0]==="app") {
    const chain=collectMultiBeta(e);
    if(chain.args.length>=2) {
      // Match the retained evaluator's application-entry and beta-reduction
      // obligations once per raw redex, then compile all substitutions into one
      // explicit materialization.
      for(let i=0;i<chain.args.length;i++) {
        this.tick();
        this.need("application");
        this.need("reduction");
      }
      const reduced=materializeMultiBeta(this,chain.body,chain.args);
      return multiBetaSpineWhnf(this,reduced);
    }
  }
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

// Universe-instantiating declaration bodies are a pure tree transform.
// The independent separator established that replacing its recursive walker
// with this explicit work stack changes no protected verdict.
Kernel.prototype.instantiateDeclaration = function(ref,term) {
  this.tick();
  const d=this.env.get(ref[1]),ps=d.levelParams??[],args=ref[2]??[];
  if(ps.length!==args.length) this.reject("universe-arity");
  if(!ps.length) return term;
  this.need("universes");
  const sub=new Map(ps.map((p,i)=>[p,args[i]]));
  const work=[{kind:"visit",e:term}],vals=[];
  while(work.length) {
    const f=work.pop();
    if(f.kind==="build") {
      if(f.tag==="proj") {
        vals.push(this.make("proj",f.name,f.index,vals.pop()));
      } else {
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
        vals.push(this.make(f.tag,...xs));
      }
      continue;
    }
    const e=f.e;
    this.tick();
    if(e[0]==="sort") {
      vals.push(this.make("sort",stackLevelSub(this,e[1],sub)));
    } else if(e[0]==="const") {
      vals.push(e.length===2?e:this.make("const",e[1],e[2].map(u=>stackLevelSub(this,u,sub))));
    } else if(e[0]==="var"||e[0]==="nat"||e[0]==="strlit") {
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

// Full continuation evaluator, activated only by the host-stack fallback.
function continuationInfer(root,rootCtx) {
  let e=root,ctx=rootCtx,value,returning=false;
  const kont=[];

  while(true) {
    if(!returning) {
      if(Array.isArray(e) && e[0]==="app") {
        this.tick();
        this.need("application");
        kont.push({kind:"app-fn",arg:e[2],ctx});
        e=e[1];
        continue;
      }

      if(Array.isArray(e) && e[0]==="lam") {
        this.tick();
        this.need("binders");
        this.sortOf(e[1],ctx);
        kont.push({kind:"lam",domain:e[1]});
        ctx=[...ctx,e[1]];
        e=e[2];
        continue;
      }

      if(Array.isArray(e) && e[0]==="let") {
        this.tick();
        this.need("reduction");
        this.sortOf(e[1],ctx);
        kont.push({kind:"let-value",type:e[1],valueTerm:e[2],body:e[3],ctx});
        e=e[2];
        continue;
      }

      if(Array.isArray(e) && e[0]==="pi") {
        const levels=[]; let cur=e,cctx=ctx;
        while(Array.isArray(cur) && cur[0]==="pi") {
          this.tick();
          this.need("binders");
          const a=this.sortOf(cur[1],cctx);
          levels.push(a);
          cctx=[...cctx,cur[1]];
          cur=cur[2];
        }
        let b=this.sortOf(cur,cctx),out=null;
        for(let i=levels.length-1;i>=0;i--) {
          const a=levels[i];
          const u=(typeof a==="number"&&typeof b==="number")
            ? (b===0?0:Math.max(a,b))
            : ["imax",a,b];
          out=this.make("sort",u);
          if(i>0) b=this.whnf(out)[1];
        }
        value=out;
        returning=true;
        continue;
      }

      value=baseInfer.call(this,e,ctx);
      returning=true;
      continue;
    }

    if(!kont.length) return value;
    const k=kont.pop();

    if(k.kind==="lam") {
      value=this.make("pi",k.domain,value);
      continue;
    }

    if(k.kind==="app-fn") {
      const fty=this.whnf(value);
      if(fty[0]!=="pi") this.reject("not-a-function");
      kont.push({kind:"app-arg",fty,arg:k.arg,ctx:k.ctx});
      e=k.arg;
      ctx=k.ctx;
      returning=false;
      continue;
    }

    if(k.kind==="app-arg") {
      this.equal(value,k.fty[1],k.ctx);
      value=this.substitute(k.fty[2],k.arg);
      continue;
    }

    if(k.kind==="let-value") {
      this.equal(value,k.type,k.ctx);
      e=this.substitute(k.body,k.valueTerm);
      ctx=k.ctx;
      returning=false;
      continue;
    }

    throw new Error("unknown inference continuation");
  }
};

// Fast retained inference path. Same-tag spines are flattened without replacing
// the whole evaluator; this preserves the verified local-definition economics.
Kernel.prototype.infer = function(e,ctx) {
  // The full continuation evaluator is the ordinary checker. The exact local-
  // definition fallback keeps its previously verified spine evaluator; this
  // split is independently replayed over all 188 Arena cases.
  if(this._fullStackSafe===true || !this.localDefs) return continuationInfer.call(this,e,ctx);

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
    const domains=[]; let cur=e,cctx=ctx;
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
    const levels=[]; let cur=e,cctx=ctx;
    while(Array.isArray(cur) && cur[0]==="pi") {
      this.tick();
      this.need("binders");
      const a=this.sortOf(cur[1],cctx);
      levels.push(a);
      cctx=[...cctx,cur[1]];
      cur=cur[2];
    }
    let b=this.sortOf(cur,cctx),out=null;
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
