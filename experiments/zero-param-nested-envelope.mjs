import {readFileSync,writeFileSync,mkdirSync} from "node:fs";

const CASES=[
  ["init-prelude",true],
  ["perf/grind-ring-5",true],
  ["nested-unused-param",false],
  ["nested-nonuniform-param",false]
];

function inspect(name){
  const data=readFileSync("_build/tests/"+name+".ndjson","utf8");
  const names=new Map([[0,"[]"]]),exprs=new Map(),inds=new Map(),ctorEnv=new Map();
  const nm=id=>names.get(id)??("#"+id),ex=id=>exprs.get(id)??["?",id];
  function flat(e){const xs=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){xs.push(h[2]);h=h[1];}xs.reverse();return {h,xs};}
  function walk(e,fn){if(!Array.isArray(e))return;fn(e);for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))walk(e[i],fn);}
  function hasSource(e,sources){if(!Array.isArray(e))return false;if(e[0]==="const"&&sources.has(e[1]))return true;for(let i=1;i<e.length;i++)if(Array.isArray(e[i])&&hasSource(e[i],sources))return true;return false;}
  function shift(e,a,c=0){if(!Array.isArray(e))return e;if(["sort","const","nat","strlit"].includes(e[0]))return e;if(e[0]==="var")return e[1]<c?e:["var",e[1]+a];if(e[0]==="pi"||e[0]==="lam")return[e[0],shift(e[1],a,c),shift(e[2],a,c+1)];if(e[0]==="app")return["app",shift(e[1],a,c),shift(e[2],a,c)];if(e[0]==="proj")return["proj",e[1],e[2],shift(e[3],a,c)];if(e[0]==="let")return["let",shift(e[1],a,c),shift(e[2],a,c),shift(e[3],a,c+1)];return e;}
  function subst(e,arg,d=0){if(!Array.isArray(e))return e;if(["sort","const","nat","strlit"].includes(e[0]))return e;if(e[0]==="var")return e[1]===d?shift(arg,d):e[1]>d?["var",e[1]-1]:e;if(e[0]==="pi"||e[0]==="lam")return[e[0],subst(e[1],arg,d),subst(e[2],arg,d+1)];if(e[0]==="app")return["app",subst(e[1],arg,d),subst(e[2],arg,d)];if(e[0]==="proj")return["proj",e[1],e[2],subst(e[3],arg,d)];if(e[0]==="let")return["let",subst(e[1],arg,d),subst(e[2],arg,d),subst(e[3],arg,d+1)];return e;}
  function inst(t,args){let cur=t;for(const a of args){if(cur?.[0]!=="pi")return null;cur=subst(cur[2],a);}return cur;}
  function install(b){
    for(const t of b.types??[])inds.set(nm(t.name),{
      name:nm(t.name),numParams:t.numParams??0,numIndices:t.numIndices??0,
      ctors:(t.ctors??[]).map(nm),type:ex(t.type)
    });
    for(const c of b.ctors??[])ctorEnv.set(nm(c.name),{
      name:nm(c.name),induct:nm(c.induct),numParams:c.numParams??0,type:ex(c.type)
    });
  }
  function recognize(b,lineNo){
    const sources=new Set((b.types??[]).map(t=>nm(t.name)));
    const zeroSource=(b.types??[]).length>0&&(b.types??[]).every(t=>
      (t.numParams??0)===0&&(t.numIndices??0)===0&&(t.isUnsafe===false));
    const expectedNested=(b.types??[]).reduce((n,t)=>n+(t.numNested??0),0);
    const formers=(b.types??[]).length+expectedNested;
    const found=new Map(),queue=[];
    const consider=e=>{
      const {h,xs}=flat(e);if(h?.[0]!=="const")return;
      const I=inds.get(h[1]);if(!I||I.numParams!==1||I.numIndices!==0||xs.length<1)return;
      if(!hasSource(xs[0],sources))return;
      if(!(xs[0]?.[0]==="const"&&sources.has(xs[0][1])))return;
      const key=I.name+"@"+xs[0][1];if(found.has(key))return;
      const d={name:I.name,param:xs[0][1],ctors:I.ctors};found.set(key,d);queue.push(d);
    };
    for(const c of b.ctors??[])walk(ex(c.type),consider);
    for(let qi=0;qi<queue.length;qi++){
      const d=queue[qi],I=inds.get(d.name);
      for(const cn of d.ctors){
        const c=ctorEnv.get(cn);if(!c?.type)continue;
        const t=inst(c.type,[["const",d.param]]);if(t)walk(t,consider);
      }
    }
    const discovered=[...found.values()];
    const sourceCtorSets=(b.types??[]).map(t=>(t.ctors??[]).map(nm).sort());
    const auxCtorSets=discovered.map(d=>[...d.ctors].sort());
    const expectedSets=[...sourceCtorSets,...auxCtorSets].map(x=>JSON.stringify(x)).sort();
    const recSets=(b.recs??[]).map(r=>(r.rules??[]).map(rr=>nm(rr.ctor)).sort());
    const actualSets=recSets.map(x=>JSON.stringify(x)).sort();
    const allRuleNames=new Set(recSets.flat());
    const sourceAndAux=new Set([...sourceCtorSets.flat(),...auxCtorSets.flat()]);
    const recShape=(b.recs??[]).every(r=>
      r.numMotives===formers&&r.numMinors===sourceAndAux.size);
    const exactPartition=
      expectedSets.length===actualSets.length&&expectedSets.every((x,i)=>x===actualSets[i])&&
      allRuleNames.size===sourceAndAux.size&&[...sourceAndAux].every(x=>allRuleNames.has(x));
    const exactNested=discovered.length===expectedNested;
    const recCount=(b.recs??[]).length===formers;
    return {lineNo,zeroSource,expectedNested,formers,discovered,recCount,recShape,exactPartition,exactNested,
      recognized:zeroSource&&expectedNested>0&&recCount&&recShape&&exactPartition&&exactNested};
  }

  let lineNo=0,first=null;
  for(const line of data.split(/\r?\n/)){
    if(!line.trim())continue;lineNo++;const row=JSON.parse(line);
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
    if(row.inductive){
      const b=row.inductive;
      if(!first&&(b.types??[]).some(t=>(t.numNested??0)>0))first=recognize(b,lineNo);
      install(b);
    }
  }
  return {name,first};
}

const rows=CASES.map(([name,want])=>{const r=inspect(name);return {...r,want,pass:r.first?.recognized===want};});
const clean=rows.every(r=>r.pass);
const out={experiment:"zero-param-nested-envelope",clean,rows};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/zero-param-nested-envelope.json",JSON.stringify(out,null,2)+"\n");
console.log("ZERO_PARAM_NESTED_ENVELOPE "+JSON.stringify(out));
if(!clean)process.exit(1);
