import {readFileSync} from "node:fs";
import * as K from "../genesis/kernel.mjs";

const [dumpPath]=process.argv.slice(2);
if(!dumpPath) throw new Error("usage: node con-leche-model-canonicalize-v3.mjs DUMP");
const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const dump=readFileSync(dumpPath,"utf8");

let strippedBlocks=0,canonicalizedFieldlessRecFlags=0;
const out=[];
for(const line of dump.split(/\r?\n/)){
  if(!line.trim()) continue;
  const r=JSON.parse(line);
  if(r.inductive){
    const ts=r.inductive.types??[],cs=r.inductive.ctors??[];
    if(ts.length>1||ts.some(t=>(t?.numNested??0)>0)){
      strippedBlocks++; continue;
    }
    if(ts.length===1 && cs.every(c=>(c?.numFields??-1)===0) && ts[0].isRec===true){
      ts[0].isRec=false;
      canonicalizedFieldlessRecFlags++;
    }
  }
  out.push(JSON.stringify(r));
}
const compiled=out.join("\n")+"\n";
const result=K.checkExport(compiled,caps,4_000_000);
console.log("CON_LECHE_MODEL_CANONICALIZE_V3 "+JSON.stringify({
  strippedBlocks,canonicalizedFieldlessRecFlags,
  status:result.status,reason:result.reason,steps:result.steps??null,
  parse_records:result.parse_records??null,
  frontier_declaration:result.frontier_declaration??null,
  frontier_inductive:result.frontier_inductive?.name??null,
  claim_boundary:"Experimental compiler-side canonicalization only: a single inductive with zero constructor fields cannot contain a recursive field, so isRec=true is normalized to false before the reduced kernel sees it. No kernel rule is weakened."
}));
