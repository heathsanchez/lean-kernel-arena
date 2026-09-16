import {readFileSync} from "node:fs";

for (const test of ["init-prelude","perf/grind-ring-5"]) {
  const data=readFileSync("_build/tests/"+test+".ndjson","utf8");
  const names=new Map([[0,"[]"]]);
  const nm=id=>names.get(id)??("#"+id);
  let lineNo=0,found=null;
  for(const line of data.split(/\r?\n/)){
    if(!line.trim())continue; lineNo++;
    const row=JSON.parse(line);
    if(Number.isSafeInteger(row.in)){
      if(row.str&&typeof row.str.str==="string")names.set(row.in,JSON.stringify([nm(row.str.pre),"str",row.str.str]));
      else if(row.num&&Number.isSafeInteger(row.num.i))names.set(row.in,JSON.stringify([nm(row.num.pre),"num",row.num.i]));
    }
    if(row.inductive){
      const b=row.inductive;
      const typeNames=(b.types??[]).map(t=>nm(t.name));
      if(typeNames.some(n=>n.includes("ParserDescr"))){
        found={
          test,lineNo,
          types:(b.types??[]).map(t=>({name:nm(t.name),numParams:t.numParams,numIndices:t.numIndices,numNested:t.numNested,isRec:t.isRec,isUnsafe:t.isUnsafe,isReflexive:t.isReflexive,levelParams:(t.levelParams??[]).map(nm),ctors:(t.ctors??[]).map(nm),all:(t.all??[]).map(nm)})),
          ctors:(b.ctors??[]).map(c=>({name:nm(c.name),induct:nm(c.induct),cidx:c.cidx,numParams:c.numParams,numFields:c.numFields,isUnsafe:c.isUnsafe,levelParams:(c.levelParams??[]).map(nm)})),
          recs:(b.recs??[]).map(r=>({name:nm(r.name),numParams:r.numParams,numIndices:r.numIndices,numMotives:r.numMotives,numMinors:r.numMinors,k:r.k,isUnsafe:r.isUnsafe,levelParams:(r.levelParams??[]).map(nm),all:(r.all??[]).map(nm),ruleCount:(r.rules??[]).length,rules:(r.rules??[]).map(rr=>({ctor:nm(rr.ctor),nfields:rr.nfields}))}))
        };
        break;
      }
    }
  }
  console.log("PARSERDESCR_ENVELOPE "+JSON.stringify(found??{test,missing:true}));
}
