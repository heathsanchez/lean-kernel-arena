import {readFileSync,writeFileSync,mkdirSync} from "node:fs";

function inspect(testName){
  const data=readFileSync("_build/tests/"+testName+".ndjson","utf8");
  const names=new Map([[0,"[]"]]); let lineNo=0;
  const nm=id=>names.get(id)??("#"+id);
  for(const line of data.split(/\r?\n/)){
    if(!line.trim())continue; lineNo++;
    const row=JSON.parse(line);
    if(Number.isSafeInteger(row.in)){
      if(row.str&&typeof row.str.str==="string")names.set(row.in,nm(row.str.pre)+"."+row.str.str);
      else if(row.num&&Number.isSafeInteger(row.num.i))names.set(row.in,nm(row.num.pre)+"."+row.num.i);
    }
    const v=row.inductive;
    if(!v||!Array.isArray(v.types)||!Array.isArray(v.recs)||v.recs.length===v.types.length)continue;
    const topCtors=new Set((v.ctors??[]).map(c=>nm(c.name)));
    const rules=v.recs.flatMap(r=>(r.rules??[]).map(rr=>nm(rr.ctor)));
    const uniqueRules=new Set(rules);
    const types=v.types.map(t=>({
      name:nm(t.name), all:(t.all??[]).map(nm), numNested:t.numNested,
      numTypeFormers:(t.all??[]).length+(t.numNested??0),
      ctors:(t.ctors??[]).map(nm),numParams:t.numParams,numIndices:t.numIndices,isRec:t.isRec
    }));
    const recs=v.recs.map(r=>({
      name:nm(r.name),all:(r.all??[]).map(nm),numParams:r.numParams,numIndices:r.numIndices,
      numMotives:r.numMotives,numMinors:r.numMinors,k:r.k,
      rules:(r.rules??[]).map(rr=>({ctor:nm(rr.ctor),nfields:rr.nfields}))
    }));
    const nTF=types.length===1?types[0].numTypeFormers:null;
    return {
      testName,lineNo,typeCount:v.types.length,ctorCount:(v.ctors??[]).length,recCount:v.recs.length,
      types,recs,aggregate:{
        totalRuleCount:rules.length,uniqueRuleCount:uniqueRules.size,
        topCtorCount:topCtors.size,topCtors:[...topCtors],
        ruleCtors:[...uniqueRules],
        topCtorRules:recs.map(r=>r.rules.filter(rr=>topCtors.has(rr.ctor)).map(rr=>rr.ctor)),
        recCountMatchesNumTypeFormers:nTF!==null&&v.recs.length===nTF,
        motivesMatchNumTypeFormers:nTF!==null&&v.recs.every(r=>r.numMotives===nTF),
        minorsMatchTotalRules:v.recs.every(r=>r.numMinors===rules.length),
        rulesPartitioned:uniqueRules.size===rules.length
      }
    };
  }
  return {testName,missing:true};
}
const results=[inspect("init-prelude"),inspect("perf/grind-ring-5")];
const out={experiment:"nested-inductive-export-invariants",results};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/nested-inductive-export-invariants.json",JSON.stringify(out,null,2)+"\n");
console.log("NESTED_INDUCTIVE_EXPORT_INVARIANTS "+JSON.stringify(out));
if(results.some(r=>r.missing))process.exit(1);
