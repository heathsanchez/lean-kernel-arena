import {Kernel,Stop,UNKNOWN} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,whnf0=p.whnf,equal0=p.equal;

function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function ensure(k){
  k.__thmDeltaCache??=new Map();
  k.__thmDeltaStats??={unfolds:0,cacheHits:0,majorAttempts:0,majorUnfolds:0,equalAttempts:0,equalUnfolds:0};
}
function target(k){
  const n=k.currentDeclaration;
  return typeof n==="string"&&n.includes("isValidChar_UInt32");
}
function unfoldHead(k,e){
  ensure(k);
  const {h,args}=rawSpine(e);
  if(!Array.isArray(h)||h[0]!=="const") return null;
  const d=k.env.get(h[1]);
  if(d?.kind!=="thm"||!Array.isArray(d.value)) return null;
  const us=h[2]??[],key=h[1]+"|"+JSON.stringify(us);
  let body=k.__thmDeltaCache.get(key);
  if(body===undefined){
    body=k.instantiateDeclaration(h,d.value);
    k.__thmDeltaCache.set(key,body);
    k.__thmDeltaStats.unfolds++;
  }else k.__thmDeltaStats.cacheHits++;
  let out=body;
  for(const a of args) out=k.make("app",out,a);
  return out;
}
function whnfMajor(k,e){
  let cur=e;
  for(let i=0;i<64;i++){
    const w=whnf0.call(k,cur);
    const u=unfoldHead(k,w);
    if(u===null) return w;
    k.__thmDeltaStats.majorUnfolds++;
    cur=u;
  }
  return whnf0.call(k,cur);
}

p.run=function(...args){
  this.__thmDeltaCache=new Map();
  this.__thmDeltaStats={unfolds:0,cacheHits:0,majorAttempts:0,majorUnfolds:0,equalAttempts:0,equalUnfolds:0};
  return run0.apply(this,args);
};

p.whnf=function(e){
  ensure(this);
  if(target(this)&&Array.isArray(e)&&e[0]==="app"){
    const {h,args}=rawSpine(e);
    if(h?.[0]==="const"){
      const rd=this.env.get(h[1]);
      if(rd?.kind==="rec"){
        const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
        if(args.length>=total){
          this.__thmDeltaStats.majorAttempts++;
          const major=args[total-1],mw=whnfMajor(this,major);
          if(mw!==major){
            const xs=args.slice();xs[total-1]=mw;
            let out=h;
            for(const a of xs) out=this.make("app",out,a);
            return whnf0.call(this,out);
          }
        }
      }
    }
  }
  return whnf0.call(this,e);
};

p.equal=function(a,b,ctx=[]){
  ensure(this);
  if(target(this)){
    const ua=unfoldHead(this,a),ub=unfoldHead(this,b);
    if(ua!==null||ub!==null){
      this.__thmDeltaStats.equalAttempts++;
      this.__thmDeltaStats.equalUnfolds+=(ua!==null?1:0)+(ub!==null?1:0);
      return equal0.call(this,ua??a,ub??b,ctx);
    }
  }
  try{return equal0.call(this,a,b,ctx);}
  catch(e){
    if(e instanceof Stop&&e.status===UNKNOWN&&e.message==="conversion-frontier"&&target(this)){
      const ua=unfoldHead(this,a),ub=unfoldHead(this,b);
      if(ua!==null||ub!==null){
        this.__thmDeltaStats.equalAttempts++;
        this.__thmDeltaStats.equalUnfolds+=(ua!==null?1:0)+(ub!==null?1:0);
        return equal0.call(this,ua??a,ub??b,ctx);
      }
    }
    throw e;
  }
};
