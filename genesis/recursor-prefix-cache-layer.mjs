import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype, retainedRun=p.run, retainedWhnf=p.whnf;

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function objectId(k,x){
  k.__recPrefixIds??=new WeakMap();k.__recPrefixNext??=1;
  let id=k.__recPrefixIds.get(x);
  if(id===undefined){id=k.__recPrefixNext++;k.__recPrefixIds.set(x,id);}
  return id;
}
function specialize(k,rule,rh,prefix){
  k.__recPrefixCache??=new WeakMap();
  let m=k.__recPrefixCache.get(rule);
  if(!m){m=new Map();k.__recPrefixCache.set(rule,m);}
  const key=JSON.stringify(rh[2]??[])+":"+prefix.map(x=>objectId(k,x)).join(",");
  if(m.has(key)){k.__recPrefixHits=(k.__recPrefixHits??0)+1;return m.get(key);}
  let out=k.instantiateDeclaration(rh,rule.rhs);
  out=k.appN(out,prefix);
  out=retainedWhnf.call(k,out);
  m.set(key,out);
  k.__recPrefixStores=(k.__recPrefixStores??0)+1;
  return out;
}

p.run=function(...args){
  this.__recPrefixCache=new WeakMap();
  this.__recPrefixIds=new WeakMap();
  this.__recPrefixNext=1;
  return retainedRun.apply(this,args);
};

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h:rh,args:rargs}=spine(e);
    if(Array.isArray(rh)&&rh[0]==="const"){
      const rd=this.env?.get(rh[1]);
      if(rd?.kind==="rec"){
        const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
        if(rargs.length>=total){
          const major=this.whnf(rargs[total-1]);
          const {h:mh,args:margs}=spine(major);
          const md=Array.isArray(mh)&&mh[0]==="const"?this.env.get(mh[1]):null;
          if(md?.kind==="ctor"&&md.induct===rd.induct&&margs.length===md.numParams+md.numFields){
            let ok=true;
            for(let i=0;i<rd.numParams;i++)if(!this.same(margs[i],rargs[i])){ok=false;break;}
            if(ok){
              const rule=rd.rules.find(rr=>rr.ctor===md.name);
              if(rule){
                this.need("inductive-reduction");this.need("reduction");
                const prefixLen=rd.numParams+1+rd.numMinors;
                const prefix=rargs.slice(0,prefixLen);
                let out=specialize(this,rule,rh,prefix);
                for(const field of margs.slice(md.numParams))out=this.make("app",out,field);
                for(const extra of rargs.slice(total))out=this.make("app",out,extra);
                this.__recPrefixReductions=(this.__recPrefixReductions??0)+1;
                return this.whnf(out);
              }
            }
          }
        }
      }
    }
  }
  return retainedWhnf.call(this,e);
};
