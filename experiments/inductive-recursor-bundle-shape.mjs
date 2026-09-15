import {readFileSync,writeFileSync,mkdirSync} from "node:fs";

function scan(testName) {
  const data=readFileSync("_build/tests/"+testName+".ndjson","utf8");
  const names=new Map([[0,"[]"]]);
  const found=[];
  let lineNo=0;
  const nm=id=>names.has(id)?names.get(id):("#"+id);
  for (const line of data.split(/\r?\n/)) {
    if (!line.trim()) continue;
    lineNo++;
    const row=JSON.parse(line);
    if (Number.isSafeInteger(row.in)) {
      if (row.str && typeof row.str.str==="string")
        names.set(row.in,nm(row.str.pre)+"."+row.str.str);
      else if (row.num && Number.isSafeInteger(row.num.i))
        names.set(row.in,nm(row.num.pre)+"."+row.num.i);
    }
    const v=row.inductive;
    if (!v || !Array.isArray(v.types) || !Array.isArray(v.recs) || v.recs.length===v.types.length) continue;
    found.push({
      lineNo,
      typeCount:v.types.length,
      ctorCount:Array.isArray(v.ctors)?v.ctors.length:null,
      recCount:v.recs.length,
      types:v.types.map(t=>({name:nm(t.name),numParams:t.numParams,numIndices:t.numIndices,
        numNested:t.numNested,isRec:t.isRec,isUnsafe:t.isUnsafe,isReflexive:t.isReflexive,
        ctorCount:Array.isArray(t.ctors)?t.ctors.length:null})),
      ctors:(v.ctors??[]).map(c=>({name:nm(c.name),induct:nm(c.induct),cidx:c.cidx,
        numParams:c.numParams,numFields:c.numFields,isUnsafe:c.isUnsafe})),
      recs:v.recs.map(r=>({name:nm(r.name),numParams:r.numParams,numIndices:r.numIndices,
        numMotives:r.numMotives,numMinors:r.numMinors,k:r.k,isUnsafe:r.isUnsafe,
        ruleCount:Array.isArray(r.rules)?r.rules.length:null}))
    });
    if (found.length>=5) break;
  }
  return {testName,found};
}
const out={results:[scan("init-prelude"),scan("perf/grind-ring-5")]};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/inductive-recursor-bundle-shape.json",JSON.stringify(out,null,2)+"\n");
console.log("INDUCTIVE_RECURSOR_BUNDLE_SHAPE "+JSON.stringify(out));