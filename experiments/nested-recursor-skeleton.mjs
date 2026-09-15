import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
const data=readFileSync("_build/tests/init-prelude.ndjson","utf8");
const names=new Map([[0,"[]"]]), exprs=new Map();
const nm=id=>names.get(id)??("#"+id), ex=id=>exprs.get(id)??["?",id];
function flat(e){const xs=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){xs.push(h[2]);h=h[1];}xs.reverse();return {h,xs};}
function count(root){let n=0;const st=[root],seen=new Set();while(st.length){const e=st.pop();if(!Array.isArray(e)||seen.has(e))continue;seen.add(e);n++;for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))st.push(e[i]);}return n;}
function sk(e,d=7){
 if(!Array.isArray(e))return e;
 if(d<=0)return ["…",e[0]];
 if(e[0]==="const")return ["const",e[1]];
 if(e[0]==="var")return ["v",e[1]];
 if(e[0]==="sort")return ["sort"];
 if(e[0]==="pi"||e[0]==="lam")return [e[0],sk(e[1],d-1),sk(e[2],d-1)];
 if(e[0]==="app"){const {h,xs}=flat(e);return ["@",sk(h,d-1),...xs.slice(0,10).map(x=>sk(x,d-1)),...(xs.length>10?[["…args",xs.length]]:[])];}
 if(e[0]==="let")return ["let",sk(e[1],d-1),sk(e[2],d-1),sk(e[3],d-1)];
 if(e[0]==="proj")return ["proj",e[1],e[2],sk(e[3],d-1)];
 return [e[0]];
}
let target=null,lineNo=0;
for(const line of data.split(/\r?\n/)){
 if(!line.trim())continue; lineNo++; const row=JSON.parse(line);
 if(Number.isSafeInteger(row.in)){
  if(row.str&&typeof row.str.str==="string")names.set(row.in,nm(row.str.pre)+"."+row.str.str);
  else if(row.num&&Number.isSafeInteger(row.num.i))names.set(row.in,nm(row.num.pre)+"."+row.num.i);
 }
 if(Number.isSafeInteger(row.ie)){
  let e=null,v;
  if((v=row.sort)!==undefined)e=["sort",v];
  else if((v=row.bvar)!==undefined)e=["var",v];
  else if((v=row.const)!==undefined)e=["const",nm(v.name)];
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
 const b=row.inductive;
 if(b?.types?.some(t=>(t.numNested??0)>0)){
   target={lineNo,bundle:b};
   break;
 }
}
if(!target)throw new Error("nested bundle not found");
const b=target.bundle;
const out={experiment:"nested-recursor-skeleton",lineNo:target.lineNo,
 types:b.types.map(t=>({name:nm(t.name),typeNodes:count(ex(t.type)),type:sk(ex(t.type)),numNested:t.numNested,numParams:t.numParams,numIndices:t.numIndices})),
 ctors:b.ctors.map(c=>({name:nm(c.name),induct:nm(c.induct),nparams:c.numParams,nfields:c.numFields,typeNodes:count(ex(c.type)),type:sk(ex(c.type))})),
 recs:b.recs.map(r=>({name:nm(r.name),numParams:r.numParams,numIndices:r.numIndices,numMotives:r.numMotives,numMinors:r.numMinors,
   typeNodes:count(ex(r.type)),type:sk(ex(r.type)),
   rules:r.rules.map(rr=>({ctor:nm(rr.ctor),nfields:rr.nfields,rhsNodes:count(ex(rr.rhs)),rhs:sk(ex(rr.rhs))}))
 }))
};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/nested-recursor-skeleton.json",JSON.stringify(out,null,2)+"\n");
console.log("NESTED_RECURSOR_SKELETON "+JSON.stringify(out));
