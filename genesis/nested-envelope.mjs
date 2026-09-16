// Exact validator for the narrow zero-parameter nested-inductive envelope
// observed in Lean.Syntax. It does not add a general nested-inductive kernel.
// Instead it independently reconstructs the generated mutual recursors from
// already parsed container inductives and accepts the package only when every
// exported recursor type and rule body matches exactly.
//
// On success the caller may conservatively install the source type,
// constructors and recursors as opaque typed constants. This removes
// computation power; it never invents a reduction rule.

const S=u=>["sort",u], V=i=>["var",i];
const Pi=(a,b)=>["pi",a,b], Lam=(a,b)=>["lam",a,b], App=(f,a)=>["app",f,a];
const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);

function appN(f,args){ for(const a of args) f=App(f,a); return f; }
function mkBinders(tag,types,body){
  for(let i=types.length-1;i>=0;i--) body=[tag,types[i],body];
  return body;
}
function shift(e,amount,cut=0){
  if(!Array.isArray(e)) return e;
  switch(e[0]){
    case "sort": case "const": case "nat": case "strlit": return e;
    case "var": return e[1]<cut?e:["var",e[1]+amount];
    case "pi": case "lam": return [e[0],shift(e[1],amount,cut),shift(e[2],amount,cut+1)];
    case "app": return ["app",shift(e[1],amount,cut),shift(e[2],amount,cut)];
    case "proj": return ["proj",e[1],e[2],shift(e[3],amount,cut)];
    case "let": return ["let",shift(e[1],amount,cut),shift(e[2],amount,cut),shift(e[3],amount,cut+1)];
    default: throw new Error("nested-shift:"+e[0]);
  }
}
function subst(e,arg,depth=0){
  if(!Array.isArray(e)) return e;
  switch(e[0]){
    case "sort": case "const": case "nat": case "strlit": return e;
    case "var": return e[1]===depth?shift(arg,depth):e[1]>depth?["var",e[1]-1]:e;
    case "pi": case "lam": return [e[0],subst(e[1],arg,depth),subst(e[2],arg,depth+1)];
    case "app": return ["app",subst(e[1],arg,depth),subst(e[2],arg,depth)];
    case "proj": return ["proj",e[1],e[2],subst(e[3],arg,depth)];
    case "let": return ["let",subst(e[1],arg,depth),subst(e[2],arg,depth),subst(e[3],arg,depth+1)];
    default: throw new Error("nested-subst:"+e[0]);
  }
}
function levelSub(u,sub){
  if(typeof u==="number") return u;
  if(!Array.isArray(u)) return u;
  if(u[0]==="param") return sub.has(u[1])?sub.get(u[1]):u;
  return [u[0],...u.slice(1).map(x=>levelSub(x,sub))];
}
function instLevels(e,sub){
  if(!Array.isArray(e)) return e;
  if(e[0]==="sort") return ["sort",levelSub(e[1],sub)];
  if(e[0]==="const") return e.length===3?["const",e[1],e[2].map(u=>levelSub(u,sub))]:e;
  if(e[0]==="var"||e[0]==="nat"||e[0]==="strlit") return e;
  if(e[0]==="proj") return ["proj",e[1],e[2],instLevels(e[3],sub)];
  return [e[0],...e.slice(1).map(x=>Array.isArray(x)?instLevels(x,sub):x)];
}
function instantiateForalls(type,args){
  let cur=type;
  for(const a of args){
    if(cur?.[0]!=="pi") throw new Error("nested-insufficient-foralls");
    cur=subst(cur[2],a);
  }
  return cur;
}
function spine(e){
  const args=[]; let h=e;
  while(Array.isArray(h)&&h[0]==="app"){ args.push(h[2]); h=h[1]; }
  args.reverse(); return {h,args};
}
function walk(e,fn){
  if(!Array.isArray(e)) return;
  fn(e);
  for(let i=1;i<e.length;i++) if(Array.isArray(e[i])) walk(e[i],fn);
}
function splitFields(type){
  const fields=[]; let cur=type;
  while(Array.isArray(cur)&&cur[0]==="pi"){ fields.push(cur[1]); cur=cur[2]; }
  return {fields,result:cur};
}

function validateZeroParamNestedBundle(raw,{names,exprs,decls}){
  try{
    if(!raw||!Array.isArray(raw.types)||!Array.isArray(raw.ctors)||!Array.isArray(raw.recs))
      return {ok:false,reason:"schema"};

    const nm=id=>names.get(id);
    const ex=id=>exprs.get(id);
    const sourceRaw=raw.types.length===1?raw.types[0]:null;
    if(!sourceRaw) return {ok:false,reason:"source-count"};

    const source={
      ...sourceRaw,
      name:nm(sourceRaw.name),
      levelParams:(sourceRaw.levelParams??[]).map(nm),
      all:(sourceRaw.all??[]).map(nm),
      ctors:(sourceRaw.ctors??[]).map(nm),
      type:ex(sourceRaw.type)
    };
    if(typeof source.name!=="string"||!source.type||
       source.numParams!==0||source.numIndices!==0||source.isUnsafe!==false||
       source.isRec!==true||!Number.isSafeInteger(source.numNested)||source.numNested<=0||
       source.levelParams.length!==0||
       source.all.length!==1||source.all[0]!==source.name)
      return {ok:false,reason:"source-envelope"};

    const ctors=raw.ctors.map(c=>({
      ...c,name:nm(c.name),induct:nm(c.induct),
      levelParams:(c.levelParams??[]).map(nm),type:ex(c.type)
    }));
    if(ctors.some((c,i)=>typeof c.name!=="string"||!c.type||c.induct!==source.name||
       c.isUnsafe!==false||c.numParams!==0||c.cidx!==i))
      return {ok:false,reason:"source-constructors"};
    if(!same(source.ctors,ctors.map(c=>c.name)))
      return {ok:false,reason:"source-constructor-list"};

    const recs=raw.recs.map(r=>({
      ...r,name:nm(r.name),levelParams:(r.levelParams??[]).map(nm),
      all:(r.all??[]).map(nm),type:ex(r.type),
      rules:(r.rules??[]).map(rr=>({...rr,ctor:nm(rr.ctor),rhs:ex(rr.rhs)}))
    }));
    if(recs.some(r=>typeof r.name!=="string"||!r.type||
       r.rules.some(rr=>typeof rr.ctor!=="string"||!rr.rhs)))
      return {ok:false,reason:"recursor-decode"};

    // Only previously parsed single inductives may act as nested containers.
    // They will themselves be checked by the kernel before these declarations.
    const inds=new Map(), priorCtors=new Map();
    for(const d of decls){
      if(d?.kind!=="inductive") continue;
      inds.set(d.name,d);
      for(const c of d.ctors??[]) priorCtors.set(c.name,c);
    }

    const sourceTerm=["const",source.name];
    const aux=[],seen=new Set(),queue=[];
    const consider=e=>{
      const {h,args}=spine(e);
      if(h?.[0]!=="const"||args.length!==1||!same(args[0],sourceTerm)) return;
      const I=inds.get(h[1]);
      if(!I||I.numParams!==1||I.numIndices!==0) return;
      const key=JSON.stringify(e);
      if(seen.has(key)) return;
      const a={name:I.name,term:e,ind:I};
      seen.add(key); aux.push(a); queue.push(a);
    };
    for(const c of ctors) walk(c.type,consider);
    for(let qi=0;qi<queue.length;qi++){
      const a=queue[qi],{h}=spine(a.term),us=h[2]??[];
      for(const cn of a.ind.ctorNames??[]){
        const c=priorCtors.get(cn);
        if(!c?.type) continue;
        const sub=new Map((c.levelParams??[]).map((p,i)=>[p,us[i]]));
        let t=instLevels(c.type,sub);
        t=instantiateForalls(t,[sourceTerm]);
        walk(t,consider);
      }
    }
    if(aux.length!==source.numNested)
      return {ok:false,reason:"aux-count",found:aux.map(x=>x.name)};

    const targets=[{name:source.name,term:sourceTerm,kind:"source"},
      ...aux.map(a=>({...a,kind:"aux"}))];
    const groups=targets.map(()=>[]),global=[];

    const addCtor=(targetIndex,c,constTerm,type,nfieldsExpected)=>{
      const sf=splitFields(type);
      if(!same(sf.result,targets[targetIndex].term)) throw new Error("nested-ctor-result:"+c.name);
      if(sf.fields.length!==nfieldsExpected) throw new Error("nested-ctor-fields:"+c.name);
      const x={name:c.name,targetIndex,constTerm,fields:sf.fields,result:sf.result};
      groups[targetIndex].push(x); global.push(x);
    };

    for(const c of ctors){
      const ch=c.levelParams.length?["const",c.name,c.levelParams.map(p=>["param",p])]:["const",c.name];
      addCtor(0,c,ch,c.type,c.numFields);
    }
    for(let ti=1;ti<targets.length;ti++){
      const a=targets[ti],{h}=spine(a.term),us=h[2]??[];
      for(const cn of a.ind.ctorNames??[]){
        const c=priorCtors.get(cn);
        if(!c) throw new Error("nested-missing-aux-ctor:"+cn);
        if(c.numParams!==1) throw new Error("nested-aux-ctor-params:"+cn);
        const sub=new Map((c.levelParams??[]).map((p,i)=>[p,us[i]]));
        let type=instLevels(c.type,sub);
        type=instantiateForalls(type,[sourceTerm]);
        const ch=us.length?["const",c.name,us]:["const",c.name];
        const ct=appN(ch,[sourceTerm]);
        addCtor(ti,c,ct,type,c.numFields);
      }
    }

    const m=targets.length,C=global.length;
    if(m!==1+source.numNested||recs.length!==m)
      return {ok:false,reason:"motive-count"};

    // Reject any indirect/negative recursive occurrence. The supported envelope
    // is direct source recursion or recursion through discovered positive
    // one-parameter containers only.
    const recursiveFields=[];
    for(const c of global){
      const rs=[];
      for(let j=0;j<c.fields.length;j++){
        const tj=targets.findIndex(t=>same(c.fields[j],t.term));
        if(tj>=0){ rs.push({j,tj}); continue; }
        let contains=false;
        for(const t of targets) walk(c.fields[j],x=>{ if(same(x,t.term)) contains=true; });
        if(contains) return {ok:false,reason:"non-direct-recursive-field",ctor:c.name,field:j};
      }
      recursiveFields.push(rs);
    }

    const recForTarget=new Array(m);
    for(let ti=0;ti<m;ti++){
      const want=groups[ti].map(c=>c.name);
      const matches=recs.filter(r=>same(r.rules.map(x=>x.ctor),want));
      if(matches.length!==1)
        return {ok:false,reason:"rec-target-map",target:targets[ti].name};
      recForTarget[ti]=matches[0];
    }

    const uName=recForTarget[0].levelParams?.[0];
    if(typeof uName!=="string"||
       recs.some(r=>r.levelParams.length!==1||r.levelParams[0]!==uName))
      return {ok:false,reason:"rec-universes"};
    for(const r of recs){
      if(r.numParams!==0||r.numIndices!==0||r.numMotives!==m||
         r.numMinors!==C||r.k!==false||r.isUnsafe!==false)
        return {ok:false,reason:"rec-metadata",rec:r.name};
    }

    const u=["param",uName];
    const motiveDomains=targets.map(t=>Pi(t.term,S(u)));
    const minorTypes=[];
    for(let g=0;g<C;g++){
      const c=global[g],nf=c.fields.length,outer=m+g,recsHere=recursiveFields[g];
      const ihDomains=[];
      for(let k=0;k<recsHere.length;k++){
        const {j,tj}=recsHere[k],ctx=outer+nf+k;
        ihDomains.push(App(V(ctx-1-tj),V(nf+k-1-j)));
      }
      const nh=recsHere.length,ctx=outer+nf+nh;
      const fields=c.fields.map((_,j)=>V(nf+nh-1-j));
      const ctorApp=appN(c.constTerm,fields);
      const body=App(V(ctx-1-c.targetIndex),ctorApp);
      minorTypes.push(mkBinders("pi",c.fields.concat(ihDomains),body));
    }

    const prefix=motiveDomains.concat(minorTypes),P=m+C;
    const expectedTypes=[];
    const expectedRules=[];
    for(let ti=0;ti<m;ti++)
      expectedTypes[ti]=mkBinders("pi",prefix.concat([targets[ti].term]),App(V(P-ti),V(0)));

    for(let g=0;g<C;g++){
      const c=global[g],nf=c.fields.length,recsHere=recursiveFields[g],full=P+nf;
      let minor=V(C+nf-1-g);
      const fieldVars=c.fields.map((_,j)=>V(nf-1-j));
      const ihs=recsHere.map(({j,tj})=>{
        const rr=recForTarget[tj],rc=["const",rr.name,[u]];
        const prefixVars=Array.from({length:P},(_,q)=>V(full-1-q));
        return appN(rc,prefixVars.concat([V(nf-1-j)]));
      });
      expectedRules[g]=mkBinders("lam",prefix.concat(c.fields),appN(minor,fieldVars.concat(ihs)));
    }

    for(let ti=0;ti<m;ti++){
      const r=recForTarget[ti];
      if(!same(r.type,expectedTypes[ti]))
        return {ok:false,reason:"recursor-type",rec:r.name};
      for(const rr of r.rules){
        const g=global.findIndex(c=>c.name===rr.ctor);
        if(g<0||rr.nfields!==global[g].fields.length||!same(rr.rhs,expectedRules[g]))
          return {ok:false,reason:"recursor-rule",rec:r.name,ctor:rr.ctor};
      }
    }

    // Conservative installation: retain typing only. No nested computation
    // rule is added to the kernel evaluator.
    const declarations=[
      {kind:"axiom",name:source.name,type:source.type,levelParams:source.levelParams},
      ...ctors.map(c=>({kind:"axiom",name:c.name,type:c.type,levelParams:c.levelParams})),
      ...recs.map(r=>({kind:"axiom",name:r.name,type:r.type,levelParams:r.levelParams}))
    ];
    return {ok:true,declarations,source:source.name,aux:targets.slice(1).map(t=>t.name)};
  }catch(err){
    return {ok:false,reason:String(err?.message??err)};
  }
}

export {validateZeroParamNestedBundle};
