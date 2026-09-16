import { Kernel } from "./kernel-base.mjs";

// Retained execution consequence from the lawful scoped beta-spine separator.
//
// Two-or-more consecutive raw beta redexes are materialized once with exact
// de-Bruijn capture counts. The resulting WHNF request then stays on one
// explicit application/recursor/projection continuation rather than repeatedly
// rebuilding and re-decomposing equivalent application trees.
//
// The continuation is scoped to the current multi-beta WHNF request. It is also
// used when the kernel has already entered its retained stack-safe fallback.
// No unrelated future WHNF call is captured. No typing, conversion, or
// reduction rule is added.

const retainedRun=Kernel.prototype.run;
const retainedWhnf=Kernel.prototype.whnf;

function collect(root){
  const args=[];let cur=root;
  while(Array.isArray(cur)&&cur[0]==="app"&&Array.isArray(cur[1])&&cur[1][0]==="lam"){
    args.push(cur[2]);
    cur=cur[1][2];
  }
  return {body:cur,args};
}

function materialize(k,body,args){
  const work=[{kind:"visit",term:body,capture:args.length,depth:0,extra:0}],vals=[];
  while(work.length){
    const f=work.pop();
    if(f.kind==="build"){
      let out;
      if(f.tag==="proj"){
        out=k.make("proj",f.name,f.index,vals.pop());
      }else{
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
        out=k.make(f.tag,...xs);
      }
      vals.push(out);
      continue;
    }

    const e=f.term;
    k.tick();
    switch(e[0]){
      case "sort": case "const": case "nat": case "strlit":
        vals.push(e);break;
      case "var":{
        const i=e[1];
        if(i<f.depth){vals.push(e);break;}
        const j=i-f.depth;
        if(j<f.capture){
          const argIndex=f.capture-1-j;
          work.push({kind:"visit",term:args[argIndex],capture:argIndex,depth:0,extra:f.extra+f.depth});
        }else{
          const ni=f.depth+(j-f.capture)+f.extra;
          vals.push(ni===i?e:k.make("var",ni));
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
        k.unknown("multi-beta-materialize-syntax");
    }
  }
  return vals.pop();
}

function iterativeRecWhnf(k,root){
  const frames=[];

  function rebuild(head,args){
    let out=head;
    for(const a of args) out=k.make("app",out,a);
    return out;
  }

  function flatten(term){
    const args=[];let head=term;
    while(Array.isArray(head)&&head[0]==="app"){
      k.tick();k.need("application");
      args.push(head[2]);head=head[1];
    }
    args.reverse();
    return {head,args};
  }

  function attach(term,extraArgs){
    const st=flatten(term);
    if(extraArgs?.length) st.args.push(...extraArgs);
    return st;
  }

  function resumeRec(fr,major){
    const {head:rh,args:rargs,d:rd,total}=fr;
    if(major?.[0]==="nat")major=k.natLitToConstructor(major);
    const ms=flatten(major),mh=ms.head,margs=ms.args;
    const md=mh?.[0]==="const"?k.env.get(mh[1]):null;

    if(md?.kind==="ctor"&&md.induct===rd.induct&&
       margs.length===md.numParams+md.numFields){
      let paramsMatch=true;
      for(let i=0;i<rd.numParams;i++){
        if(!k.same(margs[i],rargs[i])){paramsMatch=false;break;}
      }
      if(paramsMatch){
        const rule=rd.rules.find(rr=>rr.ctor===md.name);
        if(rule){
          k.need("inductive-reduction");k.need("reduction");
          const rhs=k.instantiateDeclaration(rh,rule.rhs);
          const prefix=rargs.slice(0,rd.numParams+1+rd.numMinors);
          const nextArgs=prefix.concat(margs.slice(md.numParams),rargs.slice(total));
          return {state:attach(rhs,nextArgs)};
        }
      }
    }

    return {value:rebuild(rh,rargs)};
  }

  let state=flatten(root);

  for(;;){
    let {head,args}=state;

    if(!Array.isArray(head))
      return retainedWhnf.call(k,rebuild(head,args));

    if(head[0]==="let"){
      k.tick();k.need("reduction");
      state=attach(k.substitute(head[3],head[2]),args);
      continue;
    }

    if(head[0]==="nat"){
      k.tick();k.need("nat-literals");
    }

    if(head[0]==="lam"){
      k.tick();
      if(args.length){
        k.need("reduction");
        state=attach(k.substitute(head[2],args[0]),args.slice(1));
        continue;
      }
    }

    if(head[0]==="proj"){
      frames.push({kind:"proj",name:head[1],index:head[2],object:head[3],args});
      state=flatten(head[3]);
      continue;
    }

    if(head[0]==="const"){
      k.tick();k.need("declarations");
      const d=k.env.get(head[1]);
      if(!d) k.reject("undeclared-constant");

      if(d.kind==="def"){
        k.need("reduction");
        state=attach(k.instantiateDeclaration(head,d.value),args);
        continue;
      }

      if(d.kind==="rec"){
        const total=d.numParams+1+d.numMinors+d.numIndices+1;
        if(args.length>=total){
          frames.push({kind:"rec",head,args,d,total});
          state=flatten(args[total-1]);
          continue;
        }
      }
    }

    let result=rebuild(head,args);
    while(frames.length){
      const fr=frames.pop();

      if(fr.kind==="proj"){
        const ms=flatten(result),mh=ms.head,margs=ms.args;
        const ind=k.env.get(fr.name);
        const ctor=ind?.kind==="inductive"&&ind.ctors?.length===1?ind.ctors[0]:null;
        if(ctor!==null&&mh?.[0]==="const"&&mh[1]===ctor){
          const pos=ind.numParams+fr.index;
          if(pos>=margs.length) k.reject("projection-out-of-range");
          state=attach(margs[pos],fr.args);
          result=null;
          break;
        }
        const p=result===fr.object
          ? k.make("proj",fr.name,fr.index,fr.object)
          : k.make("proj",fr.name,fr.index,result);
        result=rebuild(p,fr.args);
        continue;
      }

      const resumed=resumeRec(fr,result);
      if(resumed.state){
        state=resumed.state;
        result=null;
        break;
      }
      result=resumed.value;
    }
    if(result!==null) return result;
  }
}

function iterativeCached(k,e){
  if(!Array.isArray(e)||k.localDefs===true) return iterativeRecWhnf(k,e);
  k.__scopedBetaWhnfCache??=new WeakMap();
  if(k.__scopedBetaWhnfCache.has(e)) return k.__scopedBetaWhnfCache.get(e);
  const out=iterativeRecWhnf(k,e);
  k.__scopedBetaWhnfCache.set(e,out);
  return out;
}

Kernel.prototype.run=function(...args){
  this.__scopedBetaWhnfCache=new WeakMap();
  return retainedRun.apply(this,args);
};

Kernel.prototype.whnf=function(e){
  if(this._fullStackSafe===true)
    return iterativeCached(this,e);

  if(this._scopedBetaDepth)
    return iterativeCached(this,e);

  if(!Array.isArray(e)||e[0]!=="app")
    return retainedWhnf.call(this,e);

  const c=collect(e);
  if(c.args.length<2)
    return retainedWhnf.call(this,e);

  this._scopedBetaDepth=1;
  try{
    for(let i=0;i<c.args.length;i++){
      this.tick();this.need("application");this.need("reduction");
    }
    const out=materialize(this,c.body,c.args);
    return iterativeCached(this,out);
  }finally{
    this._scopedBetaDepth=0;
  }
};

