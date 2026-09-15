import {readFileSync} from "node:fs";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const conLecheCommit="c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0";
const fixtures=["inmodel_mutual.ndjson","inmodel_nested.ndjson","nested_rec.ndjson"];
const results=[];
for(const fixture of fixtures){
  const url="https://raw.githubusercontent.com/leanprover/con-leche/"+conLecheCommit+"/tests/e2e/"+fixture;
  const response=await fetch(url,{signal:AbortSignal.timeout(15000)});
  if(!response.ok)throw new Error(fixture+" fetch "+response.status);
  const input=await response.text();
  let bundles=0,mutual=0,nested=0;
  for(const line of input.split(/\r?\n/)){
    if(!line.trim())continue;
    const row=JSON.parse(line);
    if(!row.inductive)continue;
    bundles++;
    const ts=row.inductive.types??[];
    if(ts.length>1)mutual++;
    if(ts.some(t=>(t?.numNested??0)>0))nested++;
  }
  const r=K.checkExport(input,caps,1000000);
  results.push({fixture,bytes:input.length,bundles,mutual,nested,status:r.status,reason:r.reason,
    parse_records:r.parse_records??null,frontier_declaration:r.frontier_declaration??null,
    frontier_inductive:r.frontier_inductive?.name??null});
}
console.log("MINIMAL_KERNEL_MODEL_BOUNDARY "+JSON.stringify({
  conLecheCommit,
  reference:"con-leche CI 34776928200 accepts these raw streams with in-process modelling; modeller-off declines at bare block",
  currentKernelCapabilities:caps,
  results
}));
