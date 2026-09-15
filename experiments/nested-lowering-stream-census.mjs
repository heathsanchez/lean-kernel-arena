import {readFileSync,writeFileSync,mkdirSync} from "node:fs";

const TARGETS=["init-prelude","perf/grind-ring-5"];

function analyze(name){
  const data=readFileSync("_build/tests/"+name+".ndjson","utf8");
  const names=new Map([[0,"[]"]]),exprs=new Map(),inds=new Map(),ctorEnv=new Map();
  const nm=id=>names.get(id)??("#"+id),ex=id=>exprs.get(id)??["?",id];

  function flat(e){const xs=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){xs.push(h[2]);h=h[1];}xs.reverse();return {h,xs};}
  function hasConstName(e,q){if(!Array.isArray(e))return false;if(e[0]==="const"&&e[1]===q)return true;for(let i=1;i<e.length;i++)if(Array.isArray(e[i])&&hasConstName(e[i],q))return true;return false;}
  function shift(e,a,c=0){if(!Array.isArray(e))return e;if(["sort","const","nat","strlit"].includes(e[0]))return e;if(e[0]==="var")return e[1]<c?e:["var",e[1]+a];if(e[0]==="pi"||e[0]==="lam")return[e[0],shift(e[1],a,c),shift(e[2],a,c+1)];if(e[0]==="app")return["app",shift(e[1],a,c),shift(e[2],a,c)];if(e[0]==="proj")return["proj",e[1],e[2],shift(e[3],a,c)];if(e[0]==="let")return["let",shift(e[1],a,c),shift(e[2],a,c),shift(e[3],a,c+1)];return e;}
  function subst(e,arg,d=0){if(!Array.isArray(e))return e;if(["sort","const","nat","strlit"].includes(e[0]))return e;if(e[0]==="var")return e[1]===d?shift(arg,d):e[1]>d?["var",e[1]-1]:e;if(e[0]==="pi"||e[0]==="lam")return[e[0],subst(e[1],arg,d),subst(e[2],arg,d+1)];if(e[0]==="app")return["app",subst(e[1],arg,d),subst(e[2],arg,d)];if(e[0]==="proj")return["proj",e[1],e[2],subst(e[3],arg,d)];if(e[0]==="let")return["let",subst(e[1],arg,d),subst(e[2],arg,d),subst(e[3],arg,d+1)];return e;}
  function instParams(t,args){let cur=t;for(const a of args){if(cur?.[0]!=="pi")return null;cur=subst(cur[2],a);}return cur;}
  function walk(e,fn){if(!Array.isArray(e))return;fn(e);for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))walk(e[i],fn);}
  function installBase(b){
    for(const t of b.types??[])inds.set(nm(t.name),{name:nm(t.name),numParams:t.numParams??0,ctors:(t.ctors??[]).map(nm),type:ex(t.type)});
    for(const c of b.ctors??[])ctorEnv.set(nm(c.name),{name:nm(c.name),induct:nm(c.induct),type:ex(c.type),numParams:c.numParams??0});
  }
  function inspectBundle(b,lineNo){
    const mainNames=new Set((b.types??[]).map(t=>nm(t.name))),found=new Map(),queue=[];
    const consider=e=>{
      const {h,xs}=flat(e);if(h?.[0]!=="const")return;
      const I=inds.get(h[1]);if(!I||xs.length<I.numParams)return;
      const ps=xs.slice(0,I.numParams);
      if(!ps.some(a=>[...mainNames].some(q=>hasConstName(a,q))))return;
      const key=JSON.stringify([I.name,...ps]);if(found.has(key))return;
      const d={key,name:I.name,params:ps,ctors:I.ctors};found.set(key,d);queue.push(d);
    };
    for(const c of b.ctors??[])walk(ex(c.type),consider);
    for(let qi=0;qi<queue.length;qi++){
      const d=queue[qi];
      for(const cn of d.ctors){
        const c=ctorEnv.get(cn);if(!c?.type)continue;
        const t=instParams(c.type,d.params);if(t)walk(t,consider);
      }
    }
    const discovered=[...found.values()].map(d=>({name:d.name,params:d.params.map(JSON.stringify),ctors:[...d.ctors]}));
    const mainRecNames=new Set((b.types??[]).map(t=>nm(t.name)+".rec"));
    const auxRecs=(b.recs??[]).filter(r=>!mainRecNames.has(nm(r.name)));
    const auxRuleSets=auxRecs.map(r=>(r.rules??[]).map(rr=>nm(rr.ctor)).sort());
    const matched=discovered.map(d=>({name:d.name,matched:auxRuleSets.some(rs=>JSON.stringify(rs)===JSON.stringify([...d.ctors].sort()))}));
    const expectedNested=(b.types??[]).reduce((n,t)=>n+(t.numNested??0),0);
    const totalRuleNames=new Set();
    for(const r of b.recs??[])for(const rr of r.rules??[])totalRuleNames.add(nm(rr.ctor));
    const motiveCount=(b.types??[]).length+expectedNested;
    const recShape=(b.recs??[]).map(r=>({
      name:nm(r.name),numMotives:r.numMotives,numMinors:r.numMinors,
      ruleCount:(r.rules??[]).length,
      motiveOK:r.numMotives===motiveCount,
      minorsOK:r.numMinors===totalRuleNames.size
    }));
    return {
      lineNo,
      sourceTypes:(b.types??[]).map(t=>({name:nm(t.name),numNested:t.numNested??0,numParams:t.numParams??0,numIndices:t.numIndices??0})),
      expectedNested,discovered,auxRuleSets,matched,
      exactCount:discovered.length===expectedNested,
      allMatched:matched.every(x=>x.matched),
      recursorCount:(b.recs??[]).length,
      motiveCount,totalUniqueRules:totalRuleNames.size,recShape,
      allRecShapes:recShape.every(x=>x.motiveOK&&x.minorsOK)
    };
  }

  const bundles=[];let lineNo=0;
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
    const b=row.inductive;
    if(!b)continue;
    const nested=(b.types??[]).some(t=>(t.numNested??0)>0);
    if(nested)bundles.push(inspectBundle(b,lineNo));
    installBase(b);
  }
  return {name,nestedBundles:bundles.length,bundles,
    allLoweringsExact:bundles.every(b=>b.exactCount&&b.allMatched),
    allRecShapes:bundles.every(b=>b.allRecShapes)};
}

const results=TARGETS.map(analyze);
const summary={
  experiment:"nested-lowering-stream-census",
  results,
  totalNestedBundles:results.reduce((n,r)=>n+r.nestedBundles,0),
  allLoweringsExact:results.every(r=>r.allLoweringsExact),
  allRecShapes:results.every(r=>r.allRecShapes)
};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/nested-lowering-stream-census.json",JSON.stringify(summary,null,2)+"\n");
console.log("NESTED_LOWERING_STREAM_CENSUS "+JSON.stringify(summary));
if(!summary.allLoweringsExact||!summary.allRecShapes)process.exit(1);
