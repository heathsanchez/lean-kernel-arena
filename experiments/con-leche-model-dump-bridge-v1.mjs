import {readFileSync} from "node:fs";
import * as K from "../genesis/kernel.mjs";

const [rawPath,dumpPath]=process.argv.slice(2);
if(!rawPath||!dumpPath)throw new Error("usage: node con-leche-model-dump-bridge.mjs RAW DUMP");
const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const raw=readFileSync(rawPath,"utf8"),dump=readFileSync(dumpPath,"utf8");

function declarationCount(text){
  let n=0;for(const line of text.split(/\r?\n/)){if(!line.trim())continue;const r=JSON.parse(line);
    if(r.inductive||r.axiom||r.def||r.thm||r.opaque||r.quot)n++;}
  return n;
}
function complexCount(text){
  let mutual=0,nested=0,total=0;
  for(const line of text.split(/\r?\n/)){if(!line.trim())continue;const r=JSON.parse(line);if(!r.inductive)continue;
    const ts=r.inductive.types??[];
    if(ts.length>1){mutual++;total++;}
    else if(ts.some(t=>(t?.numNested??0)>0)){nested++;total++;}
  }
  return {total,mutual,nested};
}
function stripComplex(text){
  const out=[];let stripped=0;
  for(const line of text.split(/\r?\n/)){
    if(!line.trim())continue;
    const r=JSON.parse(line);
    if(r.inductive){
      const ts=r.inductive.types??[];
      if(ts.length>1||ts.some(t=>(t?.numNested??0)>0)){stripped++;continue;}
    }
    out.push(line);
  }
  return {text:out.join("\n")+"\n",stripped};
}
function check(label,input){
  const r=K.checkExport(input,caps,2_000_000);
  return {label,status:r.status,reason:r.reason,steps:r.steps??null,parse_records:r.parse_records??null,
    frontier_declaration:r.frontier_declaration??null,frontier_inductive:r.frontier_inductive?.name??null};
}
const stripped=stripComplex(dump);
const report={
  experiment:"con-leche-model-dump-bridge-v1",
  capabilities:caps,
  raw:{bytes:raw.length,declarations:declarationCount(raw),complex:complexCount(raw)},
  dump:{bytes:dump.length,declarations:declarationCount(dump),complex:complexCount(dump),
    generatedDeclarationDelta:declarationCount(dump)-declarationCount(raw)},
  stripped:{bytes:stripped.text.length,declarations:declarationCount(stripped.text),complex:complexCount(stripped.text),strippedBlocks:stripped.stripped},
  checks:[check("raw",raw),check("dump-as-is",dump),check("dump-strip-complex",stripped.text)],
  claim_boundary:"The con-leche dump is used only as an experimental compiler artifact. Our kernel verdicts remain authoritative for our checker. Stripping complex blocks is a diagnostic transformation, not claimed semantics-preserving unless the resulting stream checks."
};
console.log("CON_LECHE_MODEL_DUMP_BRIDGE "+JSON.stringify(report));
