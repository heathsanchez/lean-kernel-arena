import {readFileSync,writeFileSync,mkdirSync} from "node:fs";

const TARGETS=["init-prelude","perf/grind-ring-5"];
const S=u=>["sort",u], V=i=>["var",i], Pi=(a,b)=>["pi",a,b], Lam=(a,b)=>["lam",a,b], App=(f,a)=>["app",f,a];
const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const appN=(f,args)=>{for(const a of args)f=App(f,a);return f;};
const mkBinders=(tag,types,body)=>{for(let i=types.length-1;i>=0;i--)body=[tag,types[i],body];return body;};

function shift(e,amount,cut=0){
 if(!Array.isArray(e))return e;
 switch(e[0]){
  case "sort":case "const":case "nat":case "strlit":return e;
  case "var":return e[1]<cut?e:["var",e[1]+amount];
  case "pi":case "lam":return[e[0],shift(e[1],amount,cut),shift(e[2],amount,cut+1)];
  case "app":return["app",shift(e[1],amount,cut),shift(e[2],amount,cut)];
  case "proj":return["proj",e[1],e[2],shift(e[3],amount,cut)];
  case "let":return["let",shift(e[1],amount,cut),shift(e[2],amount,cut),shift(e[3],amount,cut+1)];
 }
 throw new Error("shift:"+e[0]);
}
function subst(e,arg,depth=0){
 if(!Array.isArray(e))return e;
 switch(e[0]){
  case "sort":case "const":case "nat":case "strlit":return e;
  case "var":return e[1]===depth?shift(arg,depth):e[1]>depth?["var",e[1]-1]:e;
  case "pi":case "lam":return[e[0],subst(e[1],arg,depth),subst(e[2],arg,depth+1)];
  case "app":return["app",subst(e[1],arg,depth),subst(e[2],arg,depth)];
  case "proj":return["proj",e[1],e[2],subst(e[3],arg,depth)];
  case "let":return["let",subst(e[1],arg,depth),subst(e[2],arg,depth),subst(e[3],arg,depth+1)];
 }
 throw new Error("subst:"+e[0]);
}
function levelSub(u,sub){
 if(typeof u==="number")return u;
 if(!Array.isArray(u))return u;
 if(u[0]==="param")return sub.has(u[1])?sub.get(u[1]):u;
 return [u[0],...u.slice(1).map(x=>levelSub(x,sub))];
}
function instLevels(e,sub){
 if(!Array.isArray(e))return e;
 if(e[0]==="sort")return["sort",levelSub(e[1],sub)];
 if(e[0]==="const")return e.length===3?["const",e[1],e[2].map(u=>levelSub(u,sub))]:e;
 if(e[0]==="var"||e[0]==="nat"||e[0]==="strlit")return e;
 if(e[0]==="proj")return["proj",e[1],e[2],instLevels(e[3],sub)];
 return[e[0],...e.slice(1).map(x=>Array.isArray(x)?instLevels(x,sub):x)];
}
function instantiateForalls(type,args){
 let cur=type;
 for(const a of args){
  if(cur?.[0]!=="pi")throw new Error("insufficient-foralls");
  cur=subst(cur[2],a);
 }
 return cur;
}
function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {h,args};}
function walk(e,fn){if(!Array.isArray(e))return;fn(e);for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))walk(e[i],fn);}
function splitFields(type){
 const fields=[];let cur=type;
 while(Array.isArray(cur)&&cur[0]==="pi"){fields.push(cur[1]);cur=cur[2];}
 return {fields,result:cur};
}

function analyze(name){
 const data=readFileSync("_build/tests/"+name+".ndjson","utf8");
 const names=new Map([[0,"[]"]]),levels=new Map([[0,0]]),exprs=new Map(),inds=new Map(),ctors=new Map();
 const nm=id=>names.get(id)??("#"+id), lv=id=>levels.get(id), ex=id=>exprs.get(id);
 let lineNo=0,answer=null;
 function decodeBundle(b){
  return{
   types:(b.types??[]).map(t=>({...t,name:nm(t.name),levelParams:(t.levelParams??[]).map(nm),all:(t.all??[]).map(nm),ctors:(t.ctors??[]).map(nm),type:ex(t.type)})),
   ctors:(b.ctors??[]).map(c=>({...c,name:nm(c.name),induct:nm(c.induct),levelParams:(c.levelParams??[]).map(nm),type:ex(c.type)})),
   recs:(b.recs??[]).map(r=>({...r,name:nm(r.name),levelParams:(r.levelParams??[]).map(nm),all:(r.all??[]).map(nm),type:ex(r.type),
    rules:(r.rules??[]).map(rr=>({...rr,ctor:nm(rr.ctor),rhs:ex(rr.rhs)}))}))
  };
 }
 function installSimple(b){
  const d=decodeBundle(b);
  for(const t of d.types)inds.set(t.name,t);
  for(const c of d.ctors)ctors.set(c.name,c);
 }
 function derive(raw){
  const b=decodeBundle(raw),source=b.types[0];
  if(b.types.length!==1||source.numParams!==0||source.numIndices!==0||source.numNested<=0||source.levelParams.length!==0)
   return {ok:false,reason:"source-envelope"};
  const sourceTerm=["const",source.name],sourceNames=new Set([source.name]);
  const aux=[],seen=new Set(),queue=[];
  const consider=e=>{
   const {h,args}=spine(e);
   if(h?.[0]!=="const"||args.length!==1||!same(args[0],sourceTerm))return;
   const I=inds.get(h[1]);
   if(!I||I.numParams!==1||I.numIndices!==0)return;
   const key=JSON.stringify(e);if(seen.has(key))return;
   const a={name:I.name,term:e,ind:I};seen.add(key);aux.push(a);queue.push(a);
  };
  for(const c of b.ctors)walk(c.type,consider);
  for(let qi=0;qi<queue.length;qi++){
   const a=queue[qi],{h}=spine(a.term),us=h[2]??[];
   for(const cn of a.ind.ctors??[]){
    const c=ctors.get(cn);if(!c)continue;
    const sub=new Map((c.levelParams??[]).map((p,i)=>[p,us[i]]));
    let t=instLevels(c.type,sub);t=instantiateForalls(t,[sourceTerm]);walk(t,consider);
   }
  }
  if(aux.length!==source.numNested)return {ok:false,reason:"aux-count",aux:aux.map(x=>x.name)};
  const targets=[{name:source.name,term:sourceTerm,kind:"source"},...aux.map(a=>({...a,kind:"aux"}))];
  const groups=[],global=[];
  const addCtor=(targetIndex,c,constTerm,type,nfieldsExpected)=>{
   const sf=splitFields(type);
   if(!same(sf.result,targets[targetIndex].term))throw new Error("ctor-result:"+c.name);
   if(sf.fields.length!==nfieldsExpected)throw new Error("ctor-fields:"+c.name);
   const x={name:c.name,targetIndex,constTerm,fields:sf.fields,result:sf.result};
   groups[targetIndex].push(x);global.push(x);
  };
  for(let i=0;i<targets.length;i++)groups.push([]);
  for(const c of b.ctors){
   const ct=c.levelParams.length?["const",c.name,c.levelParams.map(p=>["param",p])]:["const",c.name];
   addCtor(0,c,ct,c.type,c.numFields);
  }
  for(let ti=1;ti<targets.length;ti++){
   const a=targets[ti],{h}=spine(a.term),us=h[2]??[];
   for(const cn of a.ind.ctors??[]){
    const c=ctors.get(cn);if(!c)throw new Error("missing-aux-ctor:"+cn);
    if(c.numParams!==1)throw new Error("aux-ctor-params:"+cn);
    const sub=new Map((c.levelParams??[]).map((p,i)=>[p,us[i]]));
    let type=instLevels(c.type,sub);type=instantiateForalls(type,[sourceTerm]);
    const ct=us.length?["const",c.name,us]:["const",c.name];
    addCtor(ti,c,ct,type,c.numFields);
   }
  }
  const m=targets.length,C=global.length;
  if(m!==1+source.numNested)return {ok:false,reason:"motive-count"};
  const recForTarget=new Array(m);
  for(let ti=0;ti<m;ti++){
   const want=groups[ti].map(c=>c.name);
   const matches=b.recs.filter(r=>same(r.rules.map(x=>x.ctor),want));
   if(matches.length!==1)return {ok:false,reason:"rec-target-map",ti,want,matches:matches.map(x=>x.name)};
   recForTarget[ti]=matches[0];
  }
  const uName=recForTarget[0].levelParams?.[0];
  if(typeof uName!=="string"||b.recs.some(r=>r.levelParams.length!==1||r.levelParams[0]!==uName))
   return {ok:false,reason:"rec-universes"};
  for(const r of b.recs){
   if(r.numParams!==0||r.numIndices!==0||r.numMotives!==m||r.numMinors!==C||r.k!==false||r.isUnsafe!==false)
    return {ok:false,reason:"rec-metadata",rec:r.name};
  }
  const u=["param",uName];
  const motiveDomains=targets.map(t=>Pi(t.term,S(u)));
  const minorTypes=[];
  const recursiveFields=[];
  for(let g=0;g<C;g++){
   const c=global[g],nf=c.fields.length,outer=m+g,recs=[];
   for(let j=0;j<nf;j++){
    const tj=targets.findIndex(t=>same(c.fields[j],t.term));
    if(tj>=0)recs.push({j,tj});
    else {
     let contains=false;for(const t of targets)walk(c.fields[j],x=>{if(same(x,t.term))contains=true;});
     if(contains)return {ok:false,reason:"non-direct-recursive-field",ctor:c.name,field:j};
    }
   }
   const ihDomains=[];
   for(let k=0;k<recs.length;k++){
    const {j,tj}=recs[k],ctx=outer+nf+k;
    ihDomains.push(App(V(ctx-1-tj),V(nf+k-1-j)));
   }
   const nh=recs.length,ctx=outer+nf+nh;
   const fields=c.fields.map((_,j)=>V(nf+nh-1-j));
   const ctorApp=appN(c.constTerm,fields);
   const body=App(V(ctx-1-c.targetIndex),ctorApp);
   minorTypes.push(mkBinders("pi",c.fields.concat(ihDomains),body));
   recursiveFields.push(recs);
  }
  const prefix=motiveDomains.concat(minorTypes),P=m+C;
  const expectedTypes=[];
  const expectedRules=[];
  for(let ti=0;ti<m;ti++){
   const body=App(V(P-ti),V(0));
   expectedTypes[ti]=mkBinders("pi",prefix.concat([targets[ti].term]),body);
  }
  for(let g=0;g<C;g++){
   const c=global[g],nf=c.fields.length,recs=recursiveFields[g],full=P+nf;
   let minor=V(C+nf-1-g);
   const fieldVars=c.fields.map((_,j)=>V(nf-1-j));
   const ihs=recs.map(({j,tj})=>{
    const rr=recForTarget[tj],rc=["const",rr.name,[u]];
    const prefixVars=Array.from({length:P},(_,q)=>V(full-1-q));
    return appN(rc,prefixVars.concat([V(nf-1-j)]));
   });
   const rhs=appN(minor,fieldVars.concat(ihs));
   expectedRules[g]=mkBinders("lam",prefix.concat(c.fields),rhs);
  }
  const typeChecks=[],ruleChecks=[];
  for(let ti=0;ti<m;ti++){
   const r=recForTarget[ti],typeOK=same(r.type,expectedTypes[ti]);
   typeChecks.push({target:targets[ti].name,rec:r.name,typeOK});
   for(const rr of r.rules){
    const g=global.findIndex(c=>c.name===rr.ctor);
    const ok=g>=0&&same(rr.rhs,expectedRules[g])&&rr.nfields===global[g].fields.length;
    ruleChecks.push({rec:r.name,ctor:rr.ctor,ok,g});
   }
  }
  const allTypes=typeChecks.every(x=>x.typeOK),allRules=ruleChecks.length===C&&ruleChecks.every(x=>x.ok);
  // Independent negative controls: exact comparison must notice one type and one rule mutation.
  const typeMut=JSON.parse(JSON.stringify(expectedTypes[0]));typeMut.push?.("__impossible__");
  const ruleMut=JSON.parse(JSON.stringify(expectedRules[0]));
  if(Array.isArray(ruleMut)&&ruleMut[0]==="lam")ruleMut[1]=["sort",999];
  const mutantsKilled=!same(recForTarget[0].type,typeMut)&&!same(recForTarget[0].rules[0].rhs,ruleMut);
  return {ok:allTypes&&allRules&&mutantsKilled,m:targets.map(t=>t.name),global:global.map(c=>c.name),
   recMap:recForTarget.map((r,i)=>({target:targets[i].name,rec:r.name})),typeChecks,ruleChecks,allTypes,allRules,mutantsKilled};
 }
 for(const line of data.split(/\r?\n/)){
  if(!line.trim())continue;lineNo++;const row=JSON.parse(line),keys=Object.keys(row);
  if(Number.isSafeInteger(row.in)){
   if(row.str&&typeof row.str.str==="string")names.set(row.in,JSON.stringify([names.get(row.str.pre)??"[]","str",row.str.str]));
   else if(row.num&&Number.isSafeInteger(row.num.i))names.set(row.in,JSON.stringify([names.get(row.num.pre)??"[]","num",row.num.i]));
  }
  if(Number.isSafeInteger(row.il)){
   if(row.succ!==undefined){const a=lv(row.succ);levels.set(row.il,typeof a==="number"?a+1:["succ",a]);}
   else if(row.max){const a=lv(row.max[0]),b=lv(row.max[1]);levels.set(row.il,typeof a==="number"&&typeof b==="number"?Math.max(a,b):["max",a,b]);}
   else if(row.imax){const a=lv(row.imax[0]),b=lv(row.imax[1]);levels.set(row.il,typeof a==="number"&&typeof b==="number"?(b===0?0:Math.max(a,b)):["imax",a,b]);}
   else if(row.param!==undefined)levels.set(row.il,["param",nm(row.param)]);
  }
  if(Number.isSafeInteger(row.ie)){
   let e=null,v;
   if((v=row.sort)!==undefined)e=["sort",lv(v)];
   else if((v=row.bvar)!==undefined)e=["var",v];
   else if((v=row.const)!==undefined)e=v.us?.length?["const",nm(v.name),v.us.map(lv)]:["const",nm(v.name)];
   else if((v=row.app)!==undefined)e=["app",ex(v.fn),ex(v.arg)];
   else if((v=row.lam)!==undefined)e=["lam",ex(v.type),ex(v.body)];
   else if((v=row.forallE)!==undefined)e=["pi",ex(v.type),ex(v.body)];
   else if((v=row.letE)!==undefined)e=["let",ex(v.type),ex(v.value),ex(v.body)];
   else if((v=row.mdata)!==undefined)e=ex(v.expr);
   else if((v=row.proj)!==undefined)e=["proj",nm(v.typeName),v.idx,ex(v.struct)];
   else if((v=row.natVal)!==undefined)e=["nat",Number(v)];
   else if((v=row.strVal)!==undefined)e=["strlit",v];
   if(e)exprs.set(row.ie,e);
  }
  if(row.inductive){
   const nested=(row.inductive.types??[]).some(t=>(t.numNested??0)>0);
   if(nested&&!answer)answer={lineNo,result:derive(row.inductive)};
   installSimple(row.inductive);
  }
 }
 return {name,...answer};
}

const results=TARGETS.map(analyze);
const clean=results.every(x=>x.result?.ok===true);
const out={experiment:"nested-mutual-recursor-derivation",clean,results};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/nested-mutual-recursor-derivation.json",JSON.stringify(out,null,2)+"\n");
console.log("NESTED_MUTUAL_RECURSOR_DERIVATION "+JSON.stringify(out));
if(!clean)process.exit(1);
