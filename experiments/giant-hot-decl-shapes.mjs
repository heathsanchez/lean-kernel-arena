import {readFileSync} from "node:fs";

const data=readFileSync("_build/tests/perf/grind-ring-5.ndjson","utf8");
const names=new Map([[0,""]]),exprs=new Map();
const nm=id=>names.get(id)??("#"+id), ex=id=>exprs.get(id);
function head(e){let h=e,args=0;while(Array.isArray(h)&&h[0]==="app"){args++;h=h[1];}
 return Array.isArray(h)?{tag:h[0],name:h[0]==="const"?h[1]:null,args}:{tag:typeof h,args};}
function count(root){let n=0,st=[root],seen=new Set();while(st.length){const e=st.pop();if(!Array.isArray(e)||seen.has(e))continue;seen.add(e);n++;for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))st.push(e[i]);}return n;}
function sk(e,d=5){if(!Array.isArray(e))return e;if(d<=0)return ["…",e[0]];
 if(e[0]==="const")return ["const",e[1],e[2]??[]];
 if(e[0]==="var")return ["v",e[1]];if(e[0]==="sort")return ["sort",e[1]];
 if(e[0]==="proj")return ["proj",e[1],e[2],sk(e[3],d-1)];
 if(e[0]==="pi"||e[0]==="lam")return[e[0],sk(e[1],d-1),sk(e[2],d-1)];
 if(e[0]==="app")return["app",sk(e[1],d-1),sk(e[2],d-1)];
 if(e[0]==="let")return["let",sk(e[1],d-1),sk(e[2],d-1),sk(e[3],d-1)];
 return [e[0]];
}
const wanted=[/LE\.le$/, /LE\.mk$/, /^instLENat$/, /^Nat\.le$/, /^Nat\.decLe$/, /isValidChar_UInt32.*match_1_1$/];
const out=[];let lineNo=0;
for(const line of data.split(/\r?\n/)){
 if(!line.trim())continue;lineNo++;const row=JSON.parse(line);
 if(Number.isSafeInteger(row.in)){
   if(row.str&&typeof row.str.str==="string"){const p=nm(row.str.pre);names.set(row.in,p?p+"."+row.str.str:row.str.str);}
   else if(row.num&&Number.isSafeInteger(row.num.i)){const p=nm(row.num.pre);names.set(row.in,p?p+"."+row.num.i:String(row.num.i));}
 }
 if(Number.isSafeInteger(row.ie)){
   let e=null,v;
   if((v=row.sort)!==undefined)e=["sort",v];
   else if((v=row.bvar)!==undefined)e=["var",v];
   else if((v=row.const)!==undefined)e=["const",nm(v.name),v.us??[]];
   else if((v=row.app)!==undefined)e=["app",ex(v.fn),ex(v.arg)];
   else if((v=row.lam)!==undefined)e=["lam",ex(v.type),ex(v.body)];
   else if((v=row.forallE)!==undefined)e=["pi",ex(v.type),ex(v.body)];
   else if((v=row.letE)!==undefined)e=["let",ex(v.type),ex(v.value),ex(v.body)];
   else if((v=row.mdata)!==undefined)e=ex(v.expr);
   else if((v=row.proj)!==undefined)e=["proj",nm(v.typeName),v.idx,ex(v.struct)];
   else if((v=row.natVal)!==undefined)e=["nat",v];
   else if((v=row.strVal)!==undefined)e=["strlit",v];
   if(e)exprs.set(row.ie,e);
 }
 for(const tag of ["axiom","def","opaque","thm"]){
   const d=row[tag];if(!d)continue;
   const name=nm(d.name);
   if(!wanted.some(r=>r.test(name)))continue;
   const type=ex(d.type),value=("value" in d)?ex(d.value):null;
   out.push({lineNo,tag,name,type:{head:head(type),nodes:count(type),sk:sk(type)},value:value?{head:head(value),nodes:count(value),sk:sk(value)}:null});
 }
}
console.log("GIANT_HOT_DECL_SHAPES "+JSON.stringify(out));
