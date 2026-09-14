const ZERO_LEVEL=Symbol("level-constant");

// Exact level equality by zero/positive case splitting, then max-of-affine forms.
// Positive parameter p is represented as q_p + 1, with q_p ranging over N.
// On each branch imax's right argument is identically zero or strictly positive.
// At most 8 parameters; resource exhaustion remains UNKNOWN.
function levelParams(u,out=new Set(),tick=()=>{}) {
  tick();
  if(typeof u==="number") return out;
  if(u[0]==="param") out.add(u[1]);
  else for(let i=1;i<u.length;i++) levelParams(u[i],out,tick);
  return out;
}
function validateLevel(u,allowed,tick) {
  tick();
  if(Number.isSafeInteger(u)&&u>=0&&u<=1000000) return;
  if(!Array.isArray(u)) throw new Stop(REJECT,"malformed-universe");
  if(u[0]==="param"&&u.length===2&&typeof u[1]==="string") {
    if(!allowed.has(u[1])) throw new Stop(REJECT,"undeclared-universe");
    return;
  }
  const n=u[0]==="succ"?2:(u[0]==="max"||u[0]==="imax")?3:0;
  if(!n||u.length!==n) throw new Stop(REJECT,"malformed-universe");
  for(let i=1;i<u.length;i++) validateLevel(u[i],allowed,tick);
}
function levelSucc(u) { return typeof u==="number"?u+1:["succ",u]; }
function levelDefinitelyPositive(u) {
  if(typeof u==="number") return u>0;
  if(u[0]==="param") return false;
  if(u[0]==="succ") return true;
  if(u[0]==="max") return levelDefinitelyPositive(u[1])||levelDefinitelyPositive(u[2]);
  if(u[0]==="imax") return levelDefinitelyPositive(u[2]);
  return false;
}
function levelIMax(a,b) { return typeof a==="number"&&typeof b==="number"?(b===0?0:Math.max(a,b)):["imax",a,b]; }
function levelMax(a,b) { return typeof a==="number"&&typeof b==="number"?Math.max(a,b):["max",a,b]; }
function levelsLe(a,b,tick=()=>{}) { return levelsEqual(levelMax(a,b),b,tick); }
function levelSub(u,sub,tick) {
  tick();
  if(typeof u==="number") return u;
  if(u[0]==="param") return sub.has(u[1])?sub.get(u[1]):u;
  return [u[0],...u.slice(1).map(x=>levelSub(x,sub,tick))];
}
function levelsEqual(a,b,tick=()=>{}) {
  const params=[...levelParams(b,levelParams(a,new Set(),tick),tick)].sort();
  if(params.length>8) throw new Stop(UNKNOWN,"universe-case-budget");
  const clean=m=>{
    let top=-1;
    for(const [k,v] of m) {tick();if(k!==ZERO_LEVEL) top=Math.max(top,v);}
    if(top>=(m.get(ZERO_LEVEL)??0)) m.delete(ZERO_LEVEL);
    return m;
  };
  const join=(a,b)=>{
    const r=new Map(a);
    for(const [k,v] of b) {tick();r.set(k,Math.max(r.get(k)??-1,v));}
    return clean(r);
  };
  function nf(u,positive) {
    tick();
    if(typeof u==="number") return new Map([[ZERO_LEVEL,u]]);
    if(u[0]==="param") return positive.has(u[1])?new Map([[u[1],1]]):new Map([[ZERO_LEVEL,0]]);
    if(u[0]==="succ") return new Map([...nf(u[1],positive)].map(([k,v])=>[k,v+1]));
    const x=nf(u[1],positive),y=nf(u[2],positive);
    if(u[0]==="imax" && y.size===1 && y.get(ZERO_LEVEL)===0) return y;
    return join(x,y);
  }
  for(let bits=0;bits<(1<<params.length);bits++) {
    tick();
    const positive=new Set(params.filter((_,i)=>bits&(1<<i)));
    const x=clean(nf(a,positive)),y=clean(nf(b,positive));
    if(x.size!==y.size) return false;
    for(const [k,v] of x) {tick();if(y.get(k)!==v) return false;}
  }
  return true;
}
// Experimental monomorphic Lean fragment. No claim of complete Lean soundness.
// The host supplies parsing, budgets and candidate rules; retained capabilities start empty.
const ACCEPT = "ACCEPT", REJECT = "REJECT", UNKNOWN = "UNKNOWN";
const S = n => ["sort", n], V = n => ["var", n];
const Pi = (a,b) => ["pi",a,b], Lam = (a,b) => ["lam",a,b];
const App = (f,a) => ["app",f,a], Let = (a,v,b) => ["let",a,v,b];
const NatLit = n => ["nat",n];
const StrLit = s => ["strlit",s];
const Proj = (n,i,e) => ["proj",n,i,e];
const leanName = (...parts) => parts.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
function quotientType(kind,lps) {
  const expected={type:1,ctor:1,lift:2,ind:1}[kind];
  if(expected===undefined||!Array.isArray(lps)||lps.length!==expected) return null;
  const u=["param",lps[0]],Q=["const",leanName("Quot"),[u]],Mk=["const",leanName("Quot","mk"),[u]];
  const rel=Pi(V(0),Pi(V(1),S(0)));
  if(kind==="type") return Pi(S(u),Pi(rel,S(u)));
  if(kind==="ctor") return Pi(S(u),Pi(rel,Pi(V(1),App(App(Q,V(2)),V(1)))));
  if(kind==="lift") {
    const v=["param",lps[1]],Eq=["const",leanName("Eq"),[v]];
    const h=Pi(V(3),Pi(V(4),Pi(App(App(V(4),V(1)),V(0)),
      App(App(App(Eq,V(4)),App(V(3),V(2))),App(V(3),V(1))))));
    return Pi(S(u),Pi(rel,Pi(S(v),Pi(Pi(V(2),V(1)),
      Pi(h,Pi(App(App(Q,V(4)),V(3)),V(3)))))));
  }
  const motive=Pi(App(App(Q,V(1)),V(0)),S(0));
  const minor=Pi(V(2),App(V(1),App(App(App(Mk,V(3)),V(2)),V(0))));
  return Pi(S(u),Pi(rel,Pi(motive,Pi(minor,
    Pi(App(App(Q,V(3)),V(2)),App(V(2),V(0)))))));
}
class Stop extends Error { constructor(status, reason) { super(reason); this.status=status; } }
class Kernel {
  constructor(capabilities=[], budget=50000) {
    this.caps=new Set(capabilities); this.budget=budget;
  }
  run(term, expected, declarations=[], parameters=[]) {
    this.steps=0; this.env=new Map(); this.allocations=0; this.params=new Set(parameters); this.currentDeclaration=null; this.conversionFrontier=null;
    const start=Date.now();
    try {
      if (!this.caps.size) this.unknown("empty-present");
      this.validate(term); this.validate(expected);
      if (declarations.length) this.need("declarations");
      for (const d of declarations) {
        this.tick(); this.currentDeclaration=d?.name??null;
        if (!d || typeof d.name!=="string" || !["axiom","def","opaque","thm","quot","inductive","ctor","rec"].includes(d.kind)) this.unknown("declaration-kind");
        if(d.kind==="inductive") {
          this.need("single-inductives");
          this.addSingleInductive(d);
          continue;
        }
        if(d.kind==="thm") this.need("theorems");
        if(d.kind==="opaque") this.need("opaque-declarations");
        if(d.kind==="quot") this.need("quotients");
        if(d.kind==="ctor"||d.kind==="rec") this.need("enum-inductives");
        if (this.env.has(d.name)) this.reject("duplicate-declaration");
        const ps=d.levelParams??[];
        if(!Array.isArray(ps)||ps.some(p=>typeof p!=="string")||new Set(ps).size!==ps.length) this.reject("invalid-universe-parameters");
        this.params=new Set(ps);
        if(ps.length) this.need("universes");
        if(d.kind==="quot") { this.env.set(d.name,d); continue; }
        this.validate(d.type);
        const declSort=this.sortOf(d.type,[]);
        if(d.kind==="thm" && !levelsEqual(declSort,0,()=>this.tick())) this.reject("theorem-not-proposition");
        if (d.kind==="def" || d.kind==="opaque" || d.kind==="thm") {
          this.validate(d.value);
          this.equal(this.infer(d.value,[]),d.type);
        }
        // Install only after validation; self and forward references cannot be used.
        // Theorem bodies stay opaque because whnf unfolds only kind "def".
        this.env.set(d.name,d);
      }
      this.params=new Set(parameters);
      if ((this.caps.has("sort-direct") || this.caps.has("sort")) && term[0]==="sort" && expected[0]==="sort") {
        if(typeof term[1]==="number"&&typeof expected[1]==="number") {
          if(term[1]+1!==expected[1]) this.reject("sort-mismatch");
        } else {
          this.need("universes");
          if(!levelsEqual(levelSucc(term[1]),expected[1],()=>this.tick())) this.reject("universe-mismatch");
        }
      } else {
        this.sortOf(expected,[]);
        this.equal(this.infer(term,[]),expected);
      }
      return this.result(ACCEPT,"obligations-discharged",start);
    } catch(e) {
      if(e instanceof Stop) return this.result(e.status,e.message,start);
      if(e instanceof RangeError) return this.result(UNKNOWN,"host-stack-limit",start);
      throw e; // A programming exception is never converted into proof rejection.
    }
  }

  hasConst(e,name) {
    this.tick();
    if(e[0]==="const") return e[1]===name;
    if(e[0]==="sort"||e[0]==="var") return false;
    for(let i=1;i<e.length;i++) if(Array.isArray(e[i])&&this.hasConst(e[i],name)) return true;
    return false;
  }
  getApp(e) {
    this.tick(); const args=[];
    while(e[0]==="app") { args.push(e[2]); e=e[1]; this.tick(); }
    return [e,args.reverse()];
  }
  appN(f,args) { for(const a of args) f=this.make("app",f,a); return f; }
  bvars(n,offset=0) {
    const out=[]; for(let i=0;i<n;i++) out.push(V(offset+n-1-i)); return out;
  }
  constRef(name,lparams=[]) {
    return lparams.length?["const",name,lparams.map(p=>["param",p])]:["const",name];
  }
  instantiateForalls(type,args) {
    let cur=type;
    for(const a of args) {
      cur=this.whnf(cur);
      if(cur[0]!=="pi") this.reject("insufficient-constructor-parameters");
      cur=this.substitute(cur[2],a);
    }
    return cur;
  }
  splitAllForalls(type) {
    const domains=[]; let cur=type;
    while(true) {
      cur=this.whnf(cur);
      if(cur[0]!=="pi") return {domains,rest:cur};
      domains.push(cur[1]); cur=cur[2];
    }
  }
  mkBinders(tag,types,body) {
    for(let i=types.length-1;i>=0;i--) body=this.make(tag,types[i],body);
    return body;
  }
  isExactIndApp(type,d,shift) {
    const [head,args]=this.getApp(type);
    if(head[0]!=="const"||head[1]!==d.name) this.reject("inductive-result-head");
    const us=head[2]??[],expectedUs=d.levelParams.map(p=>["param",p]);
    if(JSON.stringify(us)!==JSON.stringify(expectedUs)) this.reject("inductive-result-universes");
    if(args.length!==d.numParams+d.numIndices) this.reject("inductive-result-arity");
    for(let i=0;i<d.numParams;i++) {
      const expected=V(shift+d.numParams-(i+1));
      if(!this.same(args[i],expected)) this.reject("inductive-result-parameter");
    }
    for(let i=d.numParams;i<args.length;i++)
      if(this.hasConst(args[i],d.name)) this.reject("inductive-in-index");
  }
  deriveTypeRecursor(d,ctorInfos,rec,motiveLevel=null) {
    const nC=ctorInfos.length,nP=d.numParams,nI=d.numIndices;
    if(motiveLevel===null) motiveLevel=["param",rec.levelParams[0]];
    const I=this.constRef(d.name,d.levelParams);
    let cur=d.type; const paramTypes=[];
    for(let i=0;i<nP;i++) {
      cur=this.whnf(cur); if(cur[0]!=="pi") this.reject("inductive-parameter-telescope");
      // Lean's generated recursor binds parameters at the weak-head-normal
      // form of their domains (e.g. outParam wrappers disappear).
      paramTypes.push(this.whnf(cur[1])); cur=cur[2];
    }
    const idxTypes=[]; let ix=cur;
    for(let i=0;i<nI;i++) {
      ix=this.whnf(ix); if(ix[0]!=="pi") this.reject("inductive-index-telescope");
      idxTypes.push(ix[1]); ix=ix[2];
    }
    const paramsInIdx=this.bvars(nP,nI),idxVars=this.bvars(nI);
    const majorForMotive=this.appN(I,paramsInIdx.concat(idxVars));
    const motiveType=this.mkBinders("pi",idxTypes.concat([majorForMotive]),S(motiveLevel));

    const minorTypes=[];
    for(const ci of ctorInfos) {
      const ps=this.bvars(nP,1);
      let ct=this.instantiateForalls(ci.type,ps);
      const fieldDomains=[];
      while(true) {
        const w=this.whnf(ct); if(w[0]!=="pi") { ct=w; break; }
        fieldDomains.push(w[1]); ct=w[2];
      }
      const nf=fieldDomains.length,hypTypes=[];
      for(let j=0;j<nf;j++) {
        let ft=this.whnf(this.shift(fieldDomains[j],nf-j));
        if(!this.hasConst(ft,d.name)) continue;
        const sp=this.splitAllForalls(ft),m=sp.domains.length;
        const [h,args]=this.getApp(sp.rest);
        if(h[0]!=="const"||h[1]!==d.name) this.reject("recursive-field-shape");
        const idxs=args.slice(nP,nP+nI);
        const motive=V(nf+m),field=V(nf-1-j);
        const fieldApp=this.appN(this.shift(field,m),this.bvars(m));
        const hypBody=this.appN(motive,idxs.concat([fieldApp]));
        hypTypes.push(this.mkBinders("pi",sp.domains,hypBody));
      }
      const nh=hypTypes.length,res=this.shift(ct,nh);
      const [,resArgs]=this.getApp(res),idxs=resArgs.slice(nP,nP+nI);
      const ps2=ps.map(p=>this.shift(p,nf+nh));
      const fields=this.bvars(nf,nh);
      const ctorApp=this.appN(this.constRef(ci.name,d.levelParams),ps2.concat(fields));
      const body=this.appN(V(nf+nh),idxs.concat([ctorApp]));
      const types=fieldDomains.concat(hypTypes.map((ht,i)=>this.shift(ht,i)));
      minorTypes.push(this.mkBinders("pi",types,body));
    }

    const types=paramTypes.concat([motiveType],minorTypes.map((mt,i)=>this.shift(mt,i)));
    let indexed=this.shift(cur,1+nC);
    for(let i=0;i<nI;i++) {
      indexed=this.whnf(indexed); if(indexed[0]!=="pi") this.reject("inductive-index-telescope");
      types.push(indexed[1]); indexed=indexed[2];
    }
    const params=this.bvars(nP,1+nC+nI),idxs=this.bvars(nI);
    const major=this.appN(I,params.concat(idxs)); types.push(major);
    const result=this.appN(V(nC+nI+1),this.bvars(nI,1).concat([V(0)]));
    const recType=this.mkBinders("pi",types,result);

    const ruleBodies=[];
    for(let ciIndex=0;ciIndex<nC;ciIndex++) {
      const ci=ctorInfos[ciIndex],prefix=[]; let rt=recType;
      for(let j=0;j<nP+1+nC;j++) {
        rt=this.whnf(rt); if(rt[0]!=="pi") this.reject("derived-recursor-prefix");
        prefix.push(rt[1]); rt=rt[2];
      }
      const ps=this.bvars(nP,1+nC);
      let ct=this.instantiateForalls(ci.type,ps);
      const fieldDomains=[];
      while(true) {
        const w=this.whnf(ct); if(w[0]!=="pi") { ct=w; break; }
        fieldDomains.push(w[1]); ct=w[2];
      }
      const nf=fieldDomains.length,minor=V(nC-(ciIndex+1)+nf),fields=this.bvars(nf),ihs=[];
      for(let j=0;j<nf;j++) {
        let ft=this.whnf(this.shift(fieldDomains[j],nf-j));
        if(!this.hasConst(ft,d.name)) continue;
        const sp=this.splitAllForalls(ft),m=sp.domains.length;
        const [,args]=this.getApp(sp.rest),ridx=args.slice(nP,nP+nI);
        const recApp=this.constRef(rec.name,rec.levelParams);
        const prefixVars=this.bvars(nP+1+nC,nf+m);
        const field=V(nf-1-j),fieldApp=this.appN(this.shift(field,m),this.bvars(m));
        const body=this.appN(recApp,prefixVars.concat(ridx,[fieldApp]));
        ihs.push(this.mkBinders("lam",sp.domains,body));
      }
      const rhs=this.appN(minor,fields.concat(ihs));
      ruleBodies.push(this.mkBinders("lam",prefix.concat(fieldDomains),rhs));
    }
    return {recType,ruleBodies};
  }
  inferProjection(typeName,idx,obj,ctx) {
    this.need("projections");
    const objType=this.whnf(this.infer(obj,ctx));
    const [head,args]=this.getApp(objType);
    if(head[0]!=="const") this.reject("projection-non-inductive");
    if(head[1]!==typeName) this.reject("projection-type-name");
    const ind=this.env.get(typeName);
    if(!ind||ind.kind!=="inductive") this.reject("projection-non-inductive");
    if(ind.numIndices!==0||ind.ctors.length!==1) this.reject("projection-not-structure");
    if(args.length!==ind.numParams) this.reject("projection-not-fully-applied");
    const ctor=this.env.get(ind.ctors[0]);
    if(!ctor||ctor.kind!=="ctor") this.reject("projection-constructor-missing");
    const cref=this.constRef(ctor.name,head[2]?.map((_,i)=>ctor.levelParams[i])??ctor.levelParams);
    // Instantiate the constructor type at the concrete universe levels carried by the object type.
    const cLevels=head[2]??[];
    let ctype=this.instantiateDeclaration(cLevels.length?["const",ctor.name,cLevels]:["const",ctor.name],ctor.type);
    ctype=this.instantiateForalls(ctype,args.slice(0,ind.numParams));
    for(let i=0;i<idx;i++) {
      ctype=this.whnf(ctype);
      if(ctype[0]!=="pi") this.reject("projection-out-of-range");
      // In Prop structures, traversing an intervening field type detects
      // dependencies that would require exposing an earlier hidden data field.
      if(ind.isProp) this.sortOf(ctype[1],ctx);
      ctype=this.substitute(ctype[2],this.make("proj",typeName,i,obj));
    }
    ctype=this.whnf(ctype);
    if(ctype[0]!=="pi") this.reject("projection-out-of-range");
    if(ind.isProp) {
      const u=this.sortOf(ctype[1],ctx);
      if(!levelsEqual(u,0,()=>this.tick())) this.reject("projection-data-from-prop");
    }
    return ctype[1];
  }
  addSingleInductive(d) {
    this.tick();
    if(d.numNested!==0 || d.isUnsafe!==false) this.reject("unsupported-inductive-envelope");
    if(d.isReflexive) this.unknown("inductive-semantics-frontier");
    if(!Array.isArray(d.levelParams)||new Set(d.levelParams).size!==d.levelParams.length)
      this.reject("invalid-universe-parameters");
    this.params=new Set(d.levelParams);
    if(d.levelParams.length) this.need("universes");
    if(this.env.has(d.name)) this.reject("duplicate-declaration");
    this.validate(d.type); this.sortOf(d.type,[]);

    let cur=d.type,ctx=[];
    for(let i=0;i<d.numParams;i++) {
      cur=this.whnf(cur); if(cur[0]!=="pi") this.reject("inductive-parameter-telescope");
      this.sortOf(cur[1],ctx); ctx.push(cur[1]); cur=cur[2];
    }
    let actualIndices=0;
    while(true) {
      const w=this.whnf(cur);
      if(w[0]!=="pi") { cur=w; break; }
      this.sortOf(w[1],ctx); ctx.push(w[1]); cur=w[2]; actualIndices++;
    }
    if(actualIndices!==d.numIndices) this.reject("inductive-index-count");
    if(cur[0]!=="sort") this.reject("inductive-not-sort");
    const indLevel=cur[1],isProp=levelsEqual(indLevel,0,()=>this.tick()),
      mayBeProp=!levelDefinitelyPositive(indLevel);
    // A universe parameter is not safely Type-valued merely because it is not
    // identically zero: it may instantiate to Prop. Such declarations use the
    // same elimination restrictions as Prop unless a structural exception applies.
    if(mayBeProp) this.need("prop-inductives");

    if(!Array.isArray(d.all)||d.all.length!==1||d.all[0]!==d.name) this.reject("inductive-all");
    if(!Array.isArray(d.ctorNames)||d.ctorNames.length!==d.ctors.length ||
       d.ctorNames.some((n,i)=>n!==d.ctors[i]?.name)) this.reject("inductive-constructor-list");

    const groupNames=[d.name,...d.ctors.map(c=>c.name),d.rec?.name];
    if(groupNames.some(n=>typeof n!=="string")||new Set(groupNames).size!==groupNames.length)
      this.reject("duplicate-declaration");
    for(const n of groupNames) if(this.env.has(n)) this.reject("duplicate-declaration");

    this.env.set(d.name,{kind:"inductive",name:d.name,type:d.type,levelParams:d.levelParams,
      numParams:d.numParams,numIndices:d.numIndices,ctors:d.ctors.map(c=>c.name),isProp,isRec:d.isRec});

    const ctorInfos=[]; let actualRec=false,recoverableData=true;
    for(let ciIndex=0;ciIndex<d.ctors.length;ciIndex++) {
      const c=d.ctors[ciIndex];
      if(c.induct!==d.name||c.cidx!==ciIndex||c.numParams!==d.numParams||c.isUnsafe!==false ||
         JSON.stringify(c.levelParams)!==JSON.stringify(d.levelParams))
        this.reject("constructor-metadata");
      this.validate(c.type); this.sortOf(c.type,[]);
      let indT=d.type,ct=c.type,cctx=[];
      for(let i=0;i<d.numParams;i++) {
        indT=this.whnf(indT);
        if(indT[0]!=="pi"||ct[0]!=="pi") this.reject("constructor-parameter-telescope");
        this.equal(indT[1],ct[1],cctx);
        cctx.push(indT[1]); indT=indT[2]; ct=ct[2];
      }
      let fields=0; const dataFields=[];
      while(ct[0]==="pi") {
        const domain=ct[1],u=this.sortOf(domain,cctx);
        const fieldFits=levelsLe(u,indLevel,()=>this.tick());
        if(mayBeProp) {
          if(!fieldFits) dataFields.push(fields);
        } else if(!fieldFits) this.reject("constructor-field-universe");
        const w=this.whnf(domain);
        if(this.hasConst(w,d.name)) {
          actualRec=true;
          const sp=this.splitAllForalls(w);
          for(const rd of sp.domains) if(this.hasConst(rd,d.name)) this.reject("negative-recursive-occurrence");
          this.isExactIndApp(sp.rest,d,fields+sp.domains.length);
        }
        cctx.push(domain); fields++; ct=ct[2];
      }
      this.isExactIndApp(ct,d,fields);
      if(fields!==c.numFields) this.reject("constructor-field-count");
      if(mayBeProp && dataFields.length) {
        const [,resultArgs]=this.getApp(ct);
        for(const ordinal of dataFields) {
          const fieldVar=V(fields-1-ordinal);
          if(!resultArgs.some(arg=>this.same(arg,fieldVar))) recoverableData=false;
        }
      }
      ctorInfos.push({...c,numFields:fields});
    }
    if(actualRec!==d.isRec) this.reject("inductive-recursion-metadata");

    const rec=d.rec;
    if(!rec||rec.numParams!==d.numParams||rec.numIndices!==d.numIndices||
       rec.numMotives!==1||rec.numMinors!==d.ctors.length||typeof rec.k!=="boolean"||rec.isUnsafe!==false||
       !Array.isArray(rec.all)||rec.all.length!==1||rec.all[0]!==d.name||
       !Array.isArray(rec.rules)||rec.rules.length!==d.ctors.length)
      this.reject("recursor-metadata");
    const expectedRecName=JSON.stringify([d.name,"str","rec"]);
    if(rec.name!==expectedRecName) this.reject("recursor-name");

    const expectedK=isProp && d.ctors.length===1 && ctorInfos[0]?.numFields===0;
    if(rec.k!==expectedK) this.reject("recursor-k");

    // Large elimination is safe if the inductive can never be Prop, or for the
    // standard empty / eta-structure / K exceptions. A merely polymorphic Sort u
    // does not count as "never Prop".
    const structureLarge=d.ctors.length===1 && !actualRec && recoverableData;
    const largeElim=!mayBeProp || d.ctors.length===0 || structureLarge || expectedK;
    let motiveLevel;
    if(!largeElim) {
      if(!Array.isArray(rec.levelParams)||rec.levelParams.length!==d.levelParams.length||
         rec.levelParams.some((p,i)=>p!==d.levelParams[i]))
        this.reject("recursor-universe-parameters");
      motiveLevel=0;
    } else {
      if(!Array.isArray(rec.levelParams)||rec.levelParams.length!==d.levelParams.length+1||
         rec.levelParams.slice(1).some((p,i)=>p!==d.levelParams[i])||
         d.levelParams.includes(rec.levelParams[0]))
        this.reject("recursor-universe-parameters");
      motiveLevel=["param",rec.levelParams[0]];
    }

    for(const c of ctorInfos)
      this.env.set(c.name,{kind:"ctor",name:c.name,type:c.type,levelParams:d.levelParams,induct:d.name,numParams:d.numParams,numFields:c.numFields});
    this.params=new Set(rec.levelParams);
    const derived=this.deriveTypeRecursor(d,ctorInfos,rec,motiveLevel);
    if(!this.same(rec.type,derived.recType)) this.reject("recursor-type:"+d.name);
    for(let i=0;i<rec.rules.length;i++) {
      const rr=rec.rules[i];
      if(rr.ctor!==ctorInfos[i].name||rr.nfields!==ctorInfos[i].numFields)
        this.reject("recursor-rule-metadata");
      if(!this.same(rr.rhs,derived.ruleBodies[i])) this.reject("recursor-rule-"+i);
    }
    this.validate(derived.recType); this.sortOf(derived.recType,[]);
    this.env.set(rec.name,{kind:"rec",name:rec.name,type:derived.recType,levelParams:rec.levelParams,
      numParams:d.numParams,numIndices:d.numIndices,numMinors:d.ctors.length,rules:rec.rules,
      induct:d.name,k:rec.k});
  }
  result(status,reason,start) {
    return {status,reason,steps:this.steps,constructed:this.allocations,elapsed_ms:Date.now()-start,
      ...(this.currentDeclaration?{frontier_declaration:this.currentDeclaration}:{}),
      ...(this.conversionFrontier?{conversion_frontier:this.conversionFrontier}:{})};
  }
  tick() { if(++this.steps>this.budget) this.unknown("budget-exhausted"); }
  need(c) { if(!this.caps.has(c)) this.unknown("missing:"+c); }
  unknown(r) { throw new Stop(UNKNOWN,r); }
  reject(r) { throw new Stop(REJECT,r); }
  make(...xs) { this.tick(); this.allocations++; return xs; }
  validate(e) {
    this.tick();
    if(!Array.isArray(e) || typeof e[0]!=="string") this.reject("malformed-term");
    const arities={sort:2,var:2,const:2,nat:2,strlit:2,proj:4,pi:3,lam:3,app:3,let:4};
    if(!(e[0] in arities)) this.unknown("syntax:"+e[0]);
    if(e.length!==arities[e[0]] && !(e[0]==="const"&&e.length===3)) this.reject("malformed-arity");
    if(e[0]==="sort"&&typeof e[1]!=="number") {
      this.need("universes");validateLevel(e[1],this.params,()=>this.tick());
    } else if(e[0]==="nat") {
      this.need("nat-literals");
      if(!Number.isSafeInteger(e[1])||e[1]<0) this.reject("malformed-nat-literal");
    } else if(e[0]==="strlit") {
      this.need("string-literals");
      if(typeof e[1]!=="string") this.reject("malformed-string-literal");
    } else if(e[0]==="proj") {
      this.need("projections");
      if(typeof e[1]!=="string"||!Number.isSafeInteger(e[2])||e[2]<0) this.reject("malformed-projection");
      this.validate(e[3]); return;
    } else if(e[0]==="sort" || e[0]==="var") {
      if(!Number.isSafeInteger(e[1]) || e[1]<0) this.reject("malformed-index");
      if(e[1]>1000000) this.unknown("index-limit");
    } else if(e[0]==="const") {
      if(typeof e[1]!=="string") this.reject("malformed-name");
      if(e.length===3) {
        if(!Array.isArray(e[2])) this.reject("malformed-universe-arguments");
        this.need("universes");for(const u of e[2]) validateLevel(u,this.params,()=>this.tick());
      }
    } else for(let i=1;i<e.length;i++) this.validate(e[i]);
  }
  shift(e,amount,cut=0) {
    this.tick();
    switch(e[0]) {
      case "sort": case "const": case "nat": case "strlit": return e;
      case "var": return e[1]<cut ? e : this.make("var",e[1]+amount);
      case "pi": case "lam": return this.make(e[0],this.shift(e[1],amount,cut),this.shift(e[2],amount,cut+1));
      case "app": return this.make("app",this.shift(e[1],amount,cut),this.shift(e[2],amount,cut));
      case "proj": return this.make("proj",e[1],e[2],this.shift(e[3],amount,cut));
      case "let": return this.make("let",this.shift(e[1],amount,cut),this.shift(e[2],amount,cut),this.shift(e[3],amount,cut+1));
      default: this.unknown("shift-syntax");
    }
  }
  substitute(e,arg,depth=0) {
    this.tick();
    switch(e[0]) {
      case "sort": case "const": case "nat": case "strlit": return e;
      case "var": return e[1]===depth ? this.shift(arg,depth) : e[1]>depth ? this.make("var",e[1]-1) : e;
      case "pi": case "lam": return this.make(e[0],this.substitute(e[1],arg,depth),this.substitute(e[2],arg,depth+1));
      case "app": return this.make("app",this.substitute(e[1],arg,depth),this.substitute(e[2],arg,depth));
      case "proj": return this.make("proj",e[1],e[2],this.substitute(e[3],arg,depth));
      case "let": return this.make("let",this.substitute(e[1],arg,depth),this.substitute(e[2],arg,depth),this.substitute(e[3],arg,depth+1));
      default: this.unknown("substitution-syntax");
    }
  }
  lowerBound(e,cut=0) {
    this.tick();
    switch(e[0]) {
      case "sort": case "const": case "nat": case "strlit": return e;
      case "var":
        if(e[1]<cut) return e;
        if(e[1]===cut) return null;
        return this.make("var",e[1]-1);
      case "pi": case "lam": {
        const a=this.lowerBound(e[1],cut),b=this.lowerBound(e[2],cut+1);
        return a===null||b===null?null:this.make(e[0],a,b);
      }
      case "app": {
        const f=this.lowerBound(e[1],cut),a=this.lowerBound(e[2],cut);
        return f===null||a===null?null:this.make("app",f,a);
      }
      case "proj": {
        const x=this.lowerBound(e[3],cut);
        return x===null?null:this.make("proj",e[1],e[2],x);
      }
      case "let": {
        const a=this.lowerBound(e[1],cut),v=this.lowerBound(e[2],cut),b=this.lowerBound(e[3],cut+1);
        return a===null||v===null||b===null?null:this.make("let",a,v,b);
      }
      default: this.unknown("eta-syntax");
    }
  }
  functionEtaContract(e) {
    this.tick();
    if(e[0]!=="lam"||e[2]?.[0]!=="app"||e[2]?.[2]?.[0]!=="var"||e[2][2][1]!==0) return null;
    return this.lowerBound(e[2][1],0);
  }
  whnf(e) {
    this.tick();
    if(e[0]==="nat") {
      this.need("nat-literals");
      const zero=["const",leanName("Nat","zero")],succ=["const",leanName("Nat","succ")];
      return e[1]===0?zero:this.make("app",succ,this.make("nat",e[1]-1));
    }
    if(e[0]==="proj") {
      this.need("projections");
      const obj=this.whnf(e[3]),ind=this.env.get(e[1]);
      if(ind?.kind==="inductive" && ind.ctors?.length===1) {
        const [head,args]=this.getApp(obj),ctor=ind.ctors[0];
        if(head[0]==="const"&&head[1]===ctor) {
          const pos=ind.numParams+e[2];
          if(pos>=args.length) this.reject("projection-out-of-range");
          return this.whnf(args[pos]);
        }
      }
      return obj===e[3]?e:this.make("proj",e[1],e[2],obj);
    }
    if(e[0]==="const") {
      this.need("declarations");
      const d=this.env.get(e[1]);
      if(!d) this.reject("undeclared-constant");
      if(d.kind==="def") {this.need("reduction"); return this.whnf(this.instantiateDeclaration(e,d.value));}
    }
    if(e[0]==="let") {this.need("reduction");return this.whnf(this.substitute(e[3],e[2]));}
    if(e[0]==="app") {
      this.need("application");
      if(this.caps.has("quotients")) {
        const [qh,qargs]=this.getApp(e);
        if(qh[0]==="const") {
          const qd=this.env.get(qh[1]);
          if(qd?.kind==="quot" && qd.quotKind==="lift" && qargs.length>=6) {
            const major=this.whnf(qargs[5]),[mh,margs]=this.getApp(major),md=mh[0]==="const"?this.env.get(mh[1]):null;
            if(md?.kind==="quot" && md.quotKind==="ctor" && margs.length===3 &&
               this.same(margs[0],qargs[0]) && this.same(margs[1],qargs[1])) {
              let out=this.make("app",qargs[3],margs[2]);
              for(const extra of qargs.slice(6)) out=this.make("app",out,extra);
              return this.whnf(out);
            }
          }
          if(qd?.kind==="quot" && qd.quotKind==="ind" && qargs.length>=5) {
            const major=this.whnf(qargs[4]),[mh,margs]=this.getApp(major),md=mh[0]==="const"?this.env.get(mh[1]):null;
            if(md?.kind==="quot" && md.quotKind==="ctor" && margs.length===3 &&
               this.same(margs[0],qargs[0]) && this.same(margs[1],qargs[1])) {
              let out=this.make("app",qargs[3],margs[2]);
              for(const extra of qargs.slice(5)) out=this.make("app",out,extra);
              return this.whnf(out);
            }
          }
        }
      }
      const [rh,rargs]=this.getApp(e);
      if(rh[0]==="const") {
        const rd=this.env.get(rh[1]);
        if(rd?.kind==="rec") {
          const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
          if(rargs.length>=total) {
            const major=this.whnf(rargs[total-1]),[mh,margs]=this.getApp(major);
            const md=mh[0]==="const"?this.env.get(mh[1]):null;
            if(md?.kind==="ctor" && md.induct===rd.induct &&
               margs.length===md.numParams+md.numFields) {
              let paramsMatch=true;
              for(let i=0;i<rd.numParams;i++) if(!this.same(margs[i],rargs[i])) { paramsMatch=false; break; }
              if(paramsMatch) {
                const rule=rd.rules.find(rr=>rr.ctor===md.name);
                if(rule) {
                  this.need("inductive-reduction"); this.need("reduction");
                  let rhs=this.instantiateDeclaration(rh,rule.rhs);
                  const prefix=rargs.slice(0,rd.numParams+1+rd.numMinors);
                  rhs=this.appN(rhs,prefix.concat(margs.slice(md.numParams)));
                  for(const extra of rargs.slice(total)) rhs=this.make("app",rhs,extra);
                  return this.whnf(rhs);
                }
              }
            }
            if(this.caps.has("rule-k") && rd.k===true && rd.rules.length===1) {
              const ind=this.env.get(rd.induct),ctor=ind?.ctors?.length===1?this.env.get(ind.ctors[0]):null;
              if(ind?.kind==="inductive" && ctor?.kind==="ctor" && ctor.numFields===0) {
                const prefixLen=rd.numParams+1+rd.numMinors;
                const idxArgs=rargs.slice(prefixLen,prefixLen+rd.numIndices);
                const recUs=rh[2]??[],ctorUs=ctor.levelParams?.length?recUs.slice(-ctor.levelParams.length):[];
                let ct=this.instantiateDeclaration(
                  ctorUs.length?["const",ctor.name,ctorUs]:["const",ctor.name],ctor.type);
                ct=this.instantiateForalls(ct,rargs.slice(0,rd.numParams));
                const [resHead,resArgs]=this.getApp(this.whnf(ct));
                const derivedIdx=resHead[0]==="const"&&resHead[1]===rd.induct
                  ?resArgs.slice(rd.numParams,rd.numParams+rd.numIndices):null;
                if(derivedIdx && derivedIdx.length===idxArgs.length &&
                   derivedIdx.every((x,i)=>this.same(this.normal(x),this.normal(idxArgs[i])))) {
                  this.need("inductive-reduction"); this.need("reduction");
                  const rule=rd.rules[0];
                  let rhs=this.instantiateDeclaration(rh,rule.rhs);
                  rhs=this.appN(rhs,rargs.slice(0,prefixLen));
                  for(const extra of rargs.slice(total)) rhs=this.make("app",rhs,extra);
                  return this.whnf(rhs);
                }
              }
            }
            if(this.caps.has("unit-eta") && rd.numIndices===0 && rd.rules.length===1 &&
               this.isUnitLikeName(rd.induct)) {
              this.need("inductive-reduction"); this.need("reduction");
              const rule=rd.rules[0];
              let rhs=this.instantiateDeclaration(rh,rule.rhs);
              const prefix=rargs.slice(0,rd.numParams+1+rd.numMinors);
              rhs=this.appN(rhs,prefix);
              for(const extra of rargs.slice(total)) rhs=this.make("app",rhs,extra);
              return this.whnf(rhs);
            }
          }
        }
      }
      const f=this.whnf(e[1]);
      if(f[0]==="lam") {this.need("reduction");return this.whnf(this.substitute(f[2],e[2]));}
      return f===e[1] ? e : this.make("app",f,e[2]);
    }
    return e;
  }
  same(a,b) {
    this.tick();
    if(a===b) return true;
    if(!Array.isArray(a)||!Array.isArray(b)||a.length!==b.length) return false;
    for(let i=0;i<a.length;i++) {
      if(Array.isArray(a[i])||Array.isArray(b[i])) {
        if(!Array.isArray(a[i])||!Array.isArray(b[i])||!this.same(a[i],b[i])) return false;
      } else if(a[i]!==b[i]) return false;
    }
    return true;
  }
  isUnitLikeName(name) {
    this.tick();
    const d=this.env.get(name);
    if(d?.unitLike===true) return true;
    if(d?.kind!=="inductive"||d.numIndices!==0||d.isRec!==false||d.ctors?.length!==1) return false;
    const c=this.env.get(d.ctors[0]);
    return c?.kind==="ctor"&&c.numFields===0;
  }
  isUnitLikeType(t) {
    this.tick();
    const [h]=this.getApp(this.whnf(t));
    return h[0]==="const"&&this.isUnitLikeName(h[1]);
  }
  structureEtaMatches(other,candidate,ctx) {
    this.tick();
    const [ch,cargs]=this.getApp(candidate);
    if(ch[0]!=="const") return false;
    const ctor=this.env.get(ch[1]);
    if(ctor?.kind!=="ctor") return false;
    const ind=this.env.get(ctor.induct);
    if(ind?.kind!=="inductive"||ind.numIndices!==0||ind.isRec!==false||
       ind.ctors?.length!==1||ind.ctors[0]!==ctor.name) return false;
    if(cargs.length!==ctor.numParams+ctor.numFields) return false;
    const [th,targs]=this.getApp(this.whnf(this.infer(other,ctx)));
    if(th[0]!=="const"||th[1]!==ind.name||targs.length!==ind.numParams) return false;
    if(!this.same(ch[2]??[],th[2]??[])) return false;
    for(let i=0;i<ind.numParams;i++) this.equal(cargs[i],targs[i],ctx);
    for(let i=0;i<ctor.numFields;i++)
      this.equal(cargs[ctor.numParams+i],this.make("proj",ind.name,i,other),ctx);
    return true;
  }
  normal(e) {
    this.tick(); e=this.whnf(e);
    if(["sort","var","const","nat","strlit"].includes(e[0])) return e;
    if(e[0]==="proj") return this.make("proj",e[1],e[2],this.normal(e[3]));
    return this.make(e[0],...e.slice(1).map(x=>this.normal(x)));
  }
  proofType(e,ctx) {
    this.tick();
    const t=this.infer(e,ctx);
    const u=this.sortOf(t,ctx);
    return levelsEqual(u,0,()=>this.tick()) ? t : null;
  }
  equal(a,b,ctx=[]) {
    this.tick();
    if(this.same(a,b)) return;
    const x=this.normal(a),y=this.normal(b);
    if(this.same(x,y)) return;
    if(x[0]==="sort" && y[0]==="sort") {
      if(typeof x[1]==="number"&&typeof y[1]==="number") this.reject("sort-mismatch");
      this.need("universes");
      if(levelsEqual(x[1],y[1],()=>this.tick())) return;
      this.reject("universe-mismatch");
    }
    if(this.caps.has("proof-irrelevance")) {
      const tx=this.proofType(x,ctx),ty=this.proofType(y,ctx);
      if(tx!==null && ty!==null) {
        this.equal(tx,ty,ctx);
        return;
      }
    }
    if(this.caps.has("function-eta")) {
      const ex=this.functionEtaContract(x);
      if(ex!==null) { this.equal(ex,y,ctx); return; }
      const ey=this.functionEtaContract(y);
      if(ey!==null) { this.equal(x,ey,ctx); return; }
    }
    if(this.caps.has("unit-eta")) {
      const tx=this.normal(this.infer(x,ctx)),ty=this.normal(this.infer(y,ctx));
      if(this.same(tx,ty)&&this.isUnitLikeType(tx)) return;
    }
    if(this.caps.has("structure-eta")) {
      if(this.structureEtaMatches(x,y,ctx)||this.structureEtaMatches(y,x,ctx)) return;
    }
    if(x[0]===y[0]) {
      if(x[0]==="app") {
        this.equal(x[1],y[1],ctx);
        this.equal(x[2],y[2],ctx);
        return;
      }
      if(x[0]==="pi" || x[0]==="lam") {
        this.equal(x[1],y[1],ctx);
        this.equal(x[2],y[2],[...ctx,x[1]]);
        return;
      }
    }
    // Eta and the remaining conversion rules are not implemented.
    // A failed comparison is not evidence of inequality.
    const lx=JSON.stringify(x),ly=JSON.stringify(y);
    this.conversionFrontier={ctx_depth:ctx.length,left_bytes:lx.length,right_bytes:ly.length,
      left:lx.slice(0,4000),right:ly.slice(0,4000)};
    this.unknown("conversion-frontier");
  }
  instantiateDeclaration(ref,term) {
    this.tick();
    const d=this.env.get(ref[1]),ps=d.levelParams??[],args=ref[2]??[];
    if(ps.length!==args.length) this.reject("universe-arity");
    if(!ps.length) return term;
    this.need("universes");
    const sub=new Map(ps.map((p,i)=>[p,args[i]]));
    const walk=e=>{
      this.tick();
      if(e[0]==="sort") return this.make("sort",levelSub(e[1],sub,()=>this.tick()));
      if(e[0]==="const") return e.length===2?e:this.make("const",e[1],e[2].map(u=>levelSub(u,sub,()=>this.tick())));
      if(e[0]==="var"||e[0]==="nat"||e[0]==="strlit") return e;
      if(e[0]==="proj") return this.make("proj",e[1],e[2],walk(e[3]));
      return this.make(e[0],...e.slice(1).map(walk));
    };
    return walk(term);
  }
  sortOf(e,ctx) {
    const t=this.whnf(this.infer(e,ctx));
    if(t[0]!=="sort") this.reject("not-a-type");
    return t[1];
  }
  infer(e,ctx) {
    this.tick();
    switch(e[0]) {
      case "sort": this.need("sort"); return this.make("sort",levelSucc(e[1]));
      case "var":
        this.need("binders");
        if(e[1]>=ctx.length) this.reject("unbound-variable");
        return this.shift(ctx[ctx.length-1-e[1]],e[1]+1);
      case "const":
        this.need("declarations");
        if(!this.env.has(e[1])) this.reject("undeclared-constant");
        return this.instantiateDeclaration(e,this.env.get(e[1]).type);
      case "nat": {
        this.need("nat-literals"); this.need("declarations");
        const n=leanName("Nat");
        if(!this.env.has(n)) this.reject("undeclared-nat");
        return ["const",n];
      }
      case "strlit": {
        this.need("string-literals"); this.need("declarations");
        const n=leanName("String");
        if(!this.env.has(n)) this.reject("undeclared-string");
        return ["const",n];
      }
      case "proj": return this.inferProjection(e[1],e[2],e[3],ctx);
      case "pi": {
        this.need("binders");
        const a=this.sortOf(e[1],ctx), b=this.sortOf(e[2],[...ctx,e[1]]);
        return this.make("sort",levelIMax(a,b));
      }
      case "lam":
        this.need("binders"); this.sortOf(e[1],ctx);
        return this.make("pi",e[1],this.infer(e[2],[...ctx,e[1]]));
      case "app": {
        this.need("application");
        const f=this.whnf(this.infer(e[1],ctx));
        if(f[0]!=="pi") this.reject("not-a-function");
        this.equal(this.infer(e[2],ctx),f[1],ctx);
        return this.substitute(f[2],e[2]);
      }
      case "let": {
        this.need("reduction"); this.sortOf(e[1],ctx);
        this.equal(this.infer(e[2],ctx),e[1],ctx);
        const bodyType=this.infer(e[3],[...ctx,e[1]]);
        return this.substitute(bodyType,e[2]);
      }
      default: this.unknown("inference-frontier");
    }
  }
}
const API={Kernel,ACCEPT,REJECT,UNKNOWN,S,V,Pi,Lam,App,Let,NatLit,StrLit,Proj};

function checkExport(input,capabilities,budget=200000) {
  const start=Date.now();let parsed=0,frontierInductive=null;
  const out=(status,reason)=>({status,reason,parse_records:parsed,elapsed_ms:Date.now()-start,
    ...(frontierInductive?{frontier_inductive:frontierInductive}:{})});
  if(!capabilities.length) return out(UNKNOWN,"empty-present");
  if(input.length>2000000) return out(UNKNOWN,"input-budget");
  const names=new Map([[0,"[]"]]),levels=new Map([[0,0]]),exprs=new Map(),decls=[];
  const fail=reason=>{throw new Stop(UNKNOWN,reason);};
  const reject=reason=>{throw new Stop(REJECT,reason);};
  const get=(m,n)=>{if(!Number.isSafeInteger(n)||n<0||!m.has(n)) fail("unresolved-reference");return m.get(n);};
  const put=(m,n,v)=>{if(!Number.isSafeInteger(n)||n<0||m.has(n)) fail("duplicate-or-invalid-index");m.set(n,v);};
  let header=false,quotStage=0;
  const quotKinds=["type","ctor","lift","ind"];
  try {
    for(const line of input.split(/\r?\n/)) {
      if(!line.trim()) continue;
      if(++parsed>100000) fail("record-budget");
      const row=JSON.parse(line);
      if(!row || Array.isArray(row)||typeof row!=="object") fail("record-schema");
      const keys=Object.keys(row);
      if(!header) {
        if(keys.length!==1 || keys[0]!=="meta" || row.meta?.format?.version!=="3.1.0") fail("export-version");
        header=true;continue;
      }
      const refs=keys.filter(k=>["in","il","ie"].includes(k));
      const tags=keys.filter(k=>!["in","il","ie"].includes(k));
      if(tags.length!==1 || refs.length>1) fail("record-schema");
      const tag=tags[0],v=row[tag];
      if(refs[0]==="in") {
        if(tag==="str" && v && typeof v.str==="string") put(names,row.in,JSON.stringify([get(names,v.pre),"str",v.str]));
        else if(tag==="num" && v && Number.isSafeInteger(v.i)&&v.i>=0) put(names,row.in,JSON.stringify([get(names,v.pre),"num",v.i]));
        else fail("name-frontier");
      } else if(refs[0]==="il") {
        if(tag==="succ") put(levels,row.il,levelSucc(get(levels,v)));
        else if((tag==="max"||tag==="imax")&&Array.isArray(v)&&v.length===2) {
          const a=get(levels,v[0]),b=get(levels,v[1]);
          put(levels,row.il,typeof a==="number"&&typeof b==="number"?(tag==="imax"&&b===0?0:Math.max(a,b)):[tag,a,b]);
        } else if(tag==="param") {
          if(!capabilities.includes("universes")) fail("universe-frontier");
          put(levels,row.il,["param",get(names,v)]);
        } else fail("universe-frontier");
      } else if(refs[0]==="ie") {
        let e;
        if(tag==="sort") e=S(get(levels,v));
        else if(tag==="bvar" && Number.isSafeInteger(v)&&v>=0) e=V(v);
        else if(tag==="const" && v && Array.isArray(v.us)) e=v.us.length?["const",get(names,v.name),v.us.map(u=>get(levels,u))]:["const",get(names,v.name)];
        else if((tag==="lam"||tag==="forallE")&&v) e=[tag==="lam"?"lam":"pi",get(exprs,v.type),get(exprs,v.body)];
        else if(tag==="app"&&v) e=App(get(exprs,v.fn),get(exprs,v.arg));
        else if(tag==="letE"&&v&&typeof v.nondep==="boolean") e=Let(get(exprs,v.type),get(exprs,v.value),get(exprs,v.body));
        else if(tag==="mdata"&&v) e=get(exprs,v.expr);
        else if(tag==="natVal"&&typeof v==="string"&&/^[0-9]+$/.test(v)) {
          if(!capabilities.includes("nat-literals")) fail("expression-frontier:natVal");
          const n=Number(v);
          if(!Number.isSafeInteger(n)) fail("nat-literal-budget");
          e=NatLit(n);
        } else if(tag==="strVal") {
          if(!capabilities.includes("string-literals")) fail("expression-frontier:strVal");
          if(typeof v!=="string") reject("malformed-string-literal");
          e=StrLit(v);
        } else if(tag==="proj"&&v) {
          if(!capabilities.includes("projections")) fail("expression-frontier:proj");
          if(!Number.isSafeInteger(v.idx)||v.idx<0) reject("malformed-projection");
          e=Proj(get(names,v.typeName),v.idx,get(exprs,v.struct));
        } else fail("expression-frontier:"+tag);
        put(exprs,row.ie,e);
      } else if(tag==="quot") {
        if(!capabilities.includes("quotients")) fail("declaration-frontier:quot");
        if(!v || !quotKinds.includes(v.kind) || !Array.isArray(v.levelParams) ||
           !Number.isSafeInteger(v.name) || !Number.isSafeInteger(v.type))
          fail("quotient-schema");
        if(quotStage>=quotKinds.length || v.kind!==quotKinds[quotStage])
          reject("quotient-package-order");
        const expectedName={
          type:leanName("Quot"),ctor:leanName("Quot","mk"),
          lift:leanName("Quot","lift"),ind:leanName("Quot","ind")
        }[v.kind];
        const name=get(names,v.name),lps=v.levelParams.map(n=>get(names,n)),type=get(exprs,v.type);
        if(name!==expectedName) reject("quotient-name");
        const expectedType=quotientType(v.kind,lps);
        if(expectedType===null) reject("quotient-universe-parameters");
        if(JSON.stringify(type)!==JSON.stringify(expectedType)) reject("quotient-type");
        decls.push({kind:"quot",quotKind:v.kind,name,type,levelParams:lps});
        quotStage++;
      } else if(tag==="inductive") {
        if(!capabilities.includes("inductive-envelope")) fail("declaration-frontier:inductive");
        if(!v || !Array.isArray(v.types) || !Array.isArray(v.ctors) || !Array.isArray(v.recs))
          fail("inductive-envelope-schema");
        // These are representation invariants of a complete Lean inductive group,
        // not positivity/elimination/typechecking claims.
        if(v.recs.length!==v.types.length) reject("inductive-recursor-count");
        const ctorNames=v.ctors.map(c=>c?.name);
        if(ctorNames.some(n=>!Number.isSafeInteger(n)) || new Set(ctorNames).size!==ctorNames.length)
          reject("inductive-constructor-identity");
        for(const rec of v.recs) {
          if(!rec || !Number.isSafeInteger(rec.numMinors)) fail("inductive-envelope-schema");
          if(rec.numMinors!==v.ctors.length) reject("inductive-minor-count");
        }

        // First complete semantic grain: a single empty inductive with no
        // parameters/indices/constructors. Its recursor has no computation
        // rules, so its full type is determined by the type constant alone.
        if(capabilities.includes("empty-inductives") && v.types.length===1 &&
           v.ctors.length===0 && v.recs.length===1) {
          const t=v.types[0],rec=v.recs[0];
          const exactTypeMeta=
            t.numParams===0 && t.numIndices===0 && t.numNested===0 &&
            t.isRec===false && t.isReflexive===false && t.isUnsafe===false &&
            Array.isArray(t.levelParams) && t.levelParams.length===0 &&
            Array.isArray(t.all) && t.all.length===1 && t.all[0]===t.name &&
            Array.isArray(t.ctors) && t.ctors.length===0;
          if(exactTypeMeta) {
            const exactRecMeta=
              rec.numParams===0 && rec.numIndices===0 && rec.numMotives===1 &&
              rec.numMinors===0 && rec.k===false && rec.isUnsafe===false &&
              Array.isArray(rec.rules) && rec.rules.length===0 &&
              Array.isArray(rec.all) && rec.all.length===1 && rec.all[0]===t.name &&
              Array.isArray(rec.levelParams) && rec.levelParams.length===1;
            if(!exactRecMeta) reject("empty-inductive-recursor-metadata");
            const tn=get(names,t.name),rn=get(names,rec.name),u=get(names,rec.levelParams[0]);
            const typeExpr=get(exprs,t.type),recExpr=get(exprs,rec.type);
            if(typeExpr?.[0]!=="sort") fail("empty-inductive-type-frontier");
            const I=["const",tn];
            const expectedRec=Pi(Pi(I,S(["param",u])),Pi(I,App(V(1),V(0))));
            if(JSON.stringify(recExpr)!==JSON.stringify(expectedRec))
              reject("empty-inductive-recursor-type");
            decls.push({kind:"axiom",name:tn,type:typeExpr,levelParams:[]});
            decls.push({kind:"axiom",name:rn,type:recExpr,levelParams:[u]});
            continue;
          }
        }
        // Next semantic grain: a single, non-dependent finite enumeration.
        // Derive the recursor from the inductive itself and validate the exporter's
        // redundant recursor data against that derivation before installing anything.
        if(capabilities.includes("enum-inductives") && v.types.length===1 &&
           v.ctors.length>0 && v.recs.length===1) {
          const it=v.types[0],rec=v.recs[0],typeExpr=get(exprs,it.type);
          const exactTypeMeta=
            it.numParams===0 && it.numIndices===0 && it.numNested===0 &&
            it.isRec===false && it.isReflexive===false && it.isUnsafe===false &&
            Array.isArray(it.levelParams) && it.levelParams.length===0 &&
            Array.isArray(it.all) && it.all.length===1 && it.all[0]===it.name &&
            Array.isArray(it.ctors) && it.ctors.length===v.ctors.length &&
            it.ctors.every((n,i)=>n===v.ctors[i]?.name);
          // This increment deliberately excludes Prop and level-polymorphic
          // enumerations; their elimination laws are a later residual.
          if(exactTypeMeta && typeExpr?.[0]==="sort" &&
             typeof typeExpr[1]==="number" && typeExpr[1]>0) {
            const tn=get(names,it.name),I=["const",tn];
            const ctors=[];
            let exactCtors=true;
            for(let i=0;i<v.ctors.length;i++) {
              const c=v.ctors[i];
              if(!c || c.induct!==it.name || c.cidx!==i || c.numParams!==0 ||
                 c.numFields!==0 || c.isUnsafe!==false ||
                 !Array.isArray(c.levelParams) || c.levelParams.length!==0) {
                exactCtors=false; break;
              }
              const cn=get(names,c.name),ce=get(exprs,c.type);
              if(JSON.stringify(ce)!==JSON.stringify(I)) { exactCtors=false; break; }
              ctors.push({name:cn,type:ce});
            }
            if(exactCtors) {
              if(!Array.isArray(rec.levelParams) || rec.levelParams.length!==1 ||
                 rec.numParams!==0 || rec.numIndices!==0 || rec.numMotives!==1 ||
                 rec.numMinors!==ctors.length || rec.k!==false || rec.isUnsafe!==false ||
                 !Array.isArray(rec.all) || rec.all.length!==1 || rec.all[0]!==it.name ||
                 !Array.isArray(rec.rules) || rec.rules.length!==ctors.length)
                reject("enum-inductive-recursor-metadata");
              const rn=get(names,rec.name),expectedRn=JSON.stringify([tn,"str","rec"]);
              if(rn!==expectedRn) reject("enum-inductive-recursor-name");
              const u=get(names,rec.levelParams[0]),motive=Pi(I,S(["param",u]));
              let expectedRec=Pi(I,App(V(ctors.length+1),V(0)));
              for(let i=ctors.length-1;i>=0;i--)
                expectedRec=Pi(App(V(i),["const",ctors[i].name]),expectedRec);
              expectedRec=Pi(motive,expectedRec);
              if(JSON.stringify(get(exprs,rec.type))!==JSON.stringify(expectedRec))
                reject("enum-inductive-recursor-type");
              for(let j=0;j<ctors.length;j++) {
                const rr=rec.rules[j];
                if(!rr || rr.ctor!==v.ctors[j].name || rr.nfields!==0)
                  reject("enum-inductive-recursor-rule-metadata");
                let rhs=V(ctors.length-1-j);
                for(let i=ctors.length-1;i>=0;i--)
                  rhs=Lam(App(V(i),["const",ctors[i].name]),rhs);
                rhs=Lam(motive,rhs);
                if(JSON.stringify(get(exprs,rr.rhs))!==JSON.stringify(rhs))
                  reject("enum-inductive-recursor-rule");
              }
              // Preserve the semantic metadata already certified above. Treating
              // constructors and recursors as plain axioms would force later
              // reduction to rediscover a lesson this grain has already proved.
              decls.push({kind:"axiom",name:tn,type:typeExpr,levelParams:[],unitLike:ctors.length===1});
              for(const c of ctors)
                decls.push({kind:"ctor",name:c.name,type:c.type,levelParams:[],
                  induct:tn,numParams:0,numFields:0});
              decls.push({kind:"rec",name:rn,type:get(exprs,rec.type),levelParams:[u],
                induct:tn,numParams:0,numIndices:0,numMinors:ctors.length,k:false,
                rules:rec.rules.map((rr,j)=>({
                  ctor:ctors[j].name,nfields:0,rhs:get(exprs,rr.rhs)
                }))});
              continue;
            }
          }
        }
        if(capabilities.includes("single-inductives") && v.types.length===1 && v.recs.length===1) {
          const it=v.types[0],rec=v.recs[0];
          if(!it||!rec||!Array.isArray(it.levelParams)||!Array.isArray(it.all)||!Array.isArray(it.ctors))
            fail("inductive-envelope-schema");
          const d={
            kind:"inductive",name:get(names,it.name),levelParams:it.levelParams.map(n=>get(names,n)),
            type:get(exprs,it.type),numParams:it.numParams,numIndices:it.numIndices,numNested:it.numNested,
            isRec:it.isRec,isUnsafe:it.isUnsafe,isReflexive:it.isReflexive,
            all:it.all.map(n=>get(names,n)),ctorNames:it.ctors.map(n=>get(names,n)),
            ctors:v.ctors.map(c=>({
              name:get(names,c.name),levelParams:(c.levelParams??[]).map(n=>get(names,n)),
              type:get(exprs,c.type),induct:get(names,c.induct),cidx:c.cidx,
              numParams:c.numParams,numFields:c.numFields,isUnsafe:c.isUnsafe
            })),
            rec:{
              name:get(names,rec.name),levelParams:(rec.levelParams??[]).map(n=>get(names,n)),
              type:get(exprs,rec.type),all:(rec.all??[]).map(n=>get(names,n)),
              numParams:rec.numParams,numIndices:rec.numIndices,numMotives:rec.numMotives,
              numMinors:rec.numMinors,k:rec.k,isUnsafe:rec.isUnsafe,
              rules:(rec.rules??[]).map(rr=>({
                ctor:get(names,rr.ctor),nfields:rr.nfields,rhs:get(exprs,rr.rhs)
              }))
            }
          };
          decls.push(d); continue;
        }
        frontierInductive={
          name:v.types.length===1&&Number.isSafeInteger(v.types[0]?.name)?(names.get(v.types[0].name)??null):null,
          bundle:v
        };
        fail("inductive-semantics-frontier");
      } else if(tag==="axiom"||tag==="def"||tag==="opaque"||tag==="thm") {
        if(tag==="thm"&&!capabilities.includes("theorems")) fail("declaration-frontier:thm");
        if(tag==="opaque"&&!capabilities.includes("opaque-declarations")) fail("declaration-frontier:opaque");
        if(!v || !Array.isArray(v.levelParams)) fail("declaration-universes");
        if(v.levelParams.length&&!capabilities.includes("universes")) fail("declaration-universes");
        // Export safety is a validity invariant, not a learned capability.
        // Unsafe/partial declarations cannot enter the trusted environment.
        if(tag==="axiom" && v.isUnsafe!==false) reject("unsafe-axiom");
        if(tag==="def" && v.safety!=="safe") reject("unsafe-definition");
        if(tag==="opaque" && v.isUnsafe!==false) reject("unsafe-opaque");
        const d={kind:tag,name:get(names,v.name),type:get(exprs,v.type),levelParams:v.levelParams.map(n=>get(names,n))};
        if(tag==="def"||tag==="opaque"||tag==="thm") d.value=get(exprs,v.value);
        decls.push(d);
      } else fail("declaration-frontier:"+tag);
    }
    if(!header) fail("missing-header");
    if(quotStage!==0 && quotStage!==quotKinds.length) reject("quotient-package-incomplete");
    const result=new Kernel(capabilities,budget).run(S(0),S(1),decls);
    return {...result,parse_records:parsed,elapsed_ms:Date.now()-start};
  } catch(e) {
    if(e instanceof Stop) return out(e.status,e.message);
    if(e instanceof SyntaxError || e instanceof TypeError || e instanceof RangeError)
      return {...out(UNKNOWN,"malformed-or-resource-limited-export"),
        diagnostic_error:String(e?.stack??e).split("\n").slice(0,4).join(" | ")};
    throw e;
  }
}

export {levelsEqual,levelSucc,levelIMax,quotientType,Stop,Kernel,ACCEPT,REJECT,UNKNOWN,S,V,Pi,Lam,App,Let,NatLit,StrLit,Proj,checkExport};
