import {readFileSync} from "node:fs";

const targets=new Set(["UInt64.ofNatLT","Bool.and'","Bool.and"]);
function decodeName(s){
  try{let x=JSON.parse(s),p=[];while(Array.isArray(x)&&x.length===3){p.push(String(x[2]));x=JSON.parse(x[0]);}return p.reverse().join(".");}
  catch{return String(s);}
}
function sketch(e,d=12){
  if(!Array.isArray(e))return e;
  if(d<=0)return["…",e[0]];
  if(e[0]==="const")return["const",decodeName(e[1]),e[2]??[]];
  if(e[0]==="proj")return["proj",decodeName(e[1]),e[2],sketch(e[3],d-1)];
  if(["var","nat","strlit","sort"].includes(e[0]))return e;
  return[e[0],...e.slice(1).map(x=>sketch(x,d-1))];
}
function parse(input){
  const names=new Map([[0,"[]"]]),levels=new Map([[0,0]]),exprs=new Map(),out=[];
  const get=(m,n)=>m.get(n),put=(m,n,v)=>m.set(n,v);
  const succ=u=>typeof u==="number"?u+1:["succ",u];
  const max=(tag,a,b)=>typeof a==="number"&&typeof b==="number"?(tag==="imax"&&b===0?0:Math.max(a,b)):[tag,a,b];
  for(const line of input.split(/\r?\n/)){
    if(!line.trim())continue;const row=JSON.parse(line),keys=Object.keys(row);
    if(keys.length===1&&keys[0]==="meta")continue;
    const refs=keys.filter(k=>["in","il","ie"].includes(k));
    const tags=keys.filter(k=>!["in","il","ie"].includes(k));
    if(tags.length!==1)continue;const tag=tags[0],v=row[tag];
    if(refs[0]==="in"){
      if(tag==="str")put(names,row.in,JSON.stringify([get(names,v.pre),"str",v.str]));
      else if(tag==="num")put(names,row.in,JSON.stringify([get(names,v.pre),"num",v.i]));
      continue;
    }
    if(refs[0]==="il"){
      if(tag==="succ")put(levels,row.il,succ(get(levels,v)));
      else if(tag==="max"||tag==="imax")put(levels,row.il,max(tag,get(levels,v[0]),get(levels,v[1])));
      else if(tag==="param")put(levels,row.il,["param",get(names,v)]);
      continue;
    }
    if(refs[0]==="ie"){
      let e=null;
      if(tag==="sort")e=["sort",get(levels,v)];
      else if(tag==="bvar")e=["var",v];
      else if(tag==="const")e=v.us?.length?["const",get(names,v.name),v.us.map(u=>get(levels,u))]:["const",get(names,v.name)];
      else if(tag==="lam"||tag==="forallE")e=[tag==="lam"?"lam":"pi",get(exprs,v.type),get(exprs,v.body)];
      else if(tag==="app")e=["app",get(exprs,v.fn),get(exprs,v.arg)];
      else if(tag==="letE")e=["let",get(exprs,v.type),get(exprs,v.value),get(exprs,v.body)];
      else if(tag==="mdata")e=get(exprs,v.expr);
      else if(tag==="natVal")e=["nat",v];
      else if(tag==="strVal")e=["strlit",v];
      else if(tag==="proj")e=["proj",get(names,v.typeName),v.idx,get(exprs,v.struct)];
      if(e!==null)put(exprs,row.ie,e);continue;
    }
    if(["axiom","def","opaque","thm"].includes(tag)&&v){
      const name=decodeName(get(names,v.name));
      if(targets.has(name))out.push({kind:tag,name,type:sketch(get(exprs,v.type)),value:v.value!==undefined?sketch(get(exprs,v.value)):null,safety:v.safety??null,isUnsafe:v.isUnsafe??null});
    }
  }
  return out;
}
for(const name of ["init-prelude","perf/grind-ring-5"]){
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  console.log("FRONTIER_DECLARATION_SHAPES "+JSON.stringify({name,declarations:parse(input)}));
}
