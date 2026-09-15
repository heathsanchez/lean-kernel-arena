import {readFileSync} from "node:fs";

const [dumpPath]=process.argv.slice(2);
if(!dumpPath) throw new Error("usage: node con-leche-model-static-deps-v5.mjs DUMP");
const dump=readFileSync(dumpPath,"utf8");

const names=new Map([[0,"[]"]]), exprs=new Map();
const get=(m,k)=>m.get(k);
function consts(e,out=new Set()){
  if(!Array.isArray(e)) return out;
  if(e[0]==="const"){out.add(e[1]);return out;}
  if(e[0]==="proj"){consts(e[3],out);return out;}
  for(let i=1;i<e.length;i++) if(Array.isArray(e[i])) consts(e[i],out);
  return out;
}
function suffix(n,parts){
  let s=n;
  for(const p of parts) s=JSON.stringify([s,"str",p]);
  return s;
}
const targetSuffix=["Tree","_model","proj_0"];
const declared=new Set();
const findings=[];
let stripped=0,canonicalized=0,recordNo=0;
for(const line of dump.split(/\r?\n/)){
  if(!line.trim()) continue;
  recordNo++;
  const r=JSON.parse(line);
  const keys=Object.keys(r),refs=keys.filter(k=>["in","il","ie"].includes(k)),tags=keys.filter(k=>!["in","il","ie"].includes(k));
  const tag=tags[0],v=r[tag];
  if(refs[0]==="in"){
    if(tag==="str") names.set(r.in,JSON.stringify([get(names,v.pre),"str",v.str]));
    else if(tag==="num") names.set(r.in,JSON.stringify([get(names,v.pre),"num",v.i]));
    continue;
  }
  if(refs[0]==="ie"){
    let e=null;
    if(tag==="sort") e=["sort",v];
    else if(tag==="bvar") e=["var",v];
    else if(tag==="const") e=["const",get(names,v.name),...(v.us?.length?[v.us]:[])];
    else if(tag==="lam"||tag==="forallE") e=[tag==="lam"?"lam":"pi",get(exprs,v.type),get(exprs,v.body)];
    else if(tag==="app") e=["app",get(exprs,v.fn),get(exprs,v.arg)];
    else if(tag==="letE") e=["let",get(exprs,v.type),get(exprs,v.value),get(exprs,v.body)];
    else if(tag==="mdata") e=get(exprs,v.expr);
    else if(tag==="natVal") e=["nat",v];
    else if(tag==="strVal") e=["strlit",v];
    else if(tag==="proj") e=["proj",get(names,v.typeName),v.idx,get(exprs,v.struct)];
    exprs.set(r.ie,e);
    continue;
  }
  if(tag==="inductive"){
    const ts=v.types??[],cs=v.ctors??[];
    if(ts.length>1||ts.some(t=>(t?.numNested??0)>0)){stripped++;continue;}
    if(ts.length===1&&cs.every(c=>(c?.numFields??-1)===0)&&ts[0].isRec===true)canonicalized++;
    for(const t of ts) declared.add(get(names,t.name));
    for(const c of cs) declared.add(get(names,c.name));
    for(const rec of v.recs??[]) declared.add(get(names,rec.name));
    continue;
  }
  if(["axiom","def","opaque","thm"].includes(tag)){
    const n=get(names,v.name);
    const deps=new Set(consts(get(exprs,v.type)));
    if(["def","opaque","thm"].includes(tag)) for(const x of consts(get(exprs,v.value))) deps.add(x);
    if(n?.includes('\"proj_0\"')){
      const missing=[...deps].filter(x=>!declared.has(x));
      findings.push({recordNo,tag,name:n,depCount:deps.size,missing,allDeps:[...deps]});
    }
    declared.add(n);
    continue;
  }
  if(tag==="quot") declared.add(get(names,v.name));
}
console.log("CON_LECHE_MODEL_STATIC_DEPS_V5 "+JSON.stringify({stripped,canonicalized,findings}));
