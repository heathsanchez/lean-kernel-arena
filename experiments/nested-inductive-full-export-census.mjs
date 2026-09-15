import {readFileSync,writeFileSync,mkdirSync} from "node:fs";

function scan(testName){
  const data=readFileSync("_build/tests/"+testName+".ndjson","utf8");
  const names=new Map([[0,"[]"]]),rows=[];let lineNo=0;
  const nm=id=>names.get(id)??("#"+id);
  for(const line of data.split(/\r?\n/)){
    if(!line.trim())continue; lineNo++;
    const row=JSON.parse(line);
    if(Number.isSafeInteger(row.in)){
      if(row.str&&typeof row.str.str==="string")names.set(row.in,nm(row.str.pre)+"."+row.str.str);
      else if(row.num&&Number.isSafeInteger(row.num.i))names.set(row.in,nm(row.num.pre)+"."+row.num.i);
    }
    const v=row.inductive;
    if(!v||!Array.isArray(v.types)||!Array.isArray(v.recs))continue;
    const nested=(v.types??[]).reduce((n,t)=>n+(t?.numNested??0),0);
    if(nested===0&&v.recs.length===v.types.length)continue;
    const typeFormers=(v.types??[]).reduce((n,t)=>n+(t?.all?.length??0)+(t?.numNested??0),0);
    const topCtors=new Set((v.ctors??[]).map(c=>nm(c.name)));
    const ruleEntries=v.recs.flatMap((r,ri)=>(r.rules??[]).map(rr=>({ri,ctor:nm(rr.ctor),nfields:rr.nfields})));
    const externalRules=ruleEntries.filter(x=>!topCtors.has(x.ctor));
    rows.push({
      lineNo,typeCount:v.types.length,ctorCount:(v.ctors??[]).length,recCount:v.recs.length,nested,typeFormers,
      types:v.types.map(t=>({name:nm(t.name),all:(t.all??[]).map(nm),ctors:(t.ctors??[]).map(nm),numNested:t.numNested,numParams:t.numParams,numIndices:t.numIndices,isRec:t.isRec,isUnsafe:t.isUnsafe})),
      recs:v.recs.map(r=>({name:nm(r.name),all:(r.all??[]).map(nm),numParams:r.numParams,numIndices:r.numIndices,numMotives:r.numMotives,numMinors:r.numMinors,k:r.k,isUnsafe:r.isUnsafe,rules:(r.rules??[]).map(rr=>({ctor:nm(rr.ctor),nfields:rr.nfields}))})),
      aggregate:{
        totalRules:ruleEntries.length,uniqueRules:new Set(ruleEntries.map(x=>x.ctor)).size,
        externalRuleCount:externalRules.length,externalRuleCtors:[...new Set(externalRules.map(x=>x.ctor))],
        recCountMatchesTypeFormers:v.recs.length===typeFormers,
        motivesUniform:v.recs.every(r=>r.numMotives===typeFormers),
        minorsUniform:v.recs.every(r=>r.numMinors===ruleEntries.length),
        rulesPartitioned:new Set(ruleEntries.map(x=>x.ctor)).size===ruleEntries.length
      }
    });
  }
  return {testName,count:rows.length,rows};
}
const results=[scan("init-prelude"),scan("perf/grind-ring-5")];
const signatures={};
for(const result of results)for(const r of result.rows){
  const sig=JSON.stringify({types:r.typeCount,ctors:r.ctorCount,recs:r.recCount,nested:r.nested,typeFormers:r.typeFormers,external:r.aggregate.externalRuleCtors.map(x=>x.split(".").slice(-2,-1)[0]??x).sort()});
  signatures[sig]=(signatures[sig]??0)+1;
}
const out={experiment:"nested-inductive-full-export-census",results,signatureCount:Object.keys(signatures).length,signatures};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/nested-inductive-full-export-census.json",JSON.stringify(out,null,2)+"\n");
console.log("NESTED_INDUCTIVE_FULL_EXPORT_CENSUS "+JSON.stringify({counts:results.map(r=>({testName:r.testName,count:r.count})),signatureCount:out.signatureCount,signatures}));
