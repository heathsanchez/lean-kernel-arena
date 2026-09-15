import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
const K=await import("file:///tmp/mathgraph-zero-nested/kernel.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const CASES=[["init-prelude","ACCEPT"],["perf/grind-ring-5","ACCEPT"],["nested-unused-param","REJECT"],["nested-nonuniform-param","either"]];

function recognizedEnvelope(b){
  const source=(b.types??[]).length===1?b.types[0]:null;
  if(!source||source.numParams!==0||source.numIndices!==0||source.isUnsafe!==false||
     !Array.isArray(source.levelParams)||source.levelParams.length!==0||
     !Number.isSafeInteger(source.numNested)||source.numNested<=0)return false;
  const recs=b.recs??[];
  if(recs.length!==1+source.numNested)return false;
  const ruleIds=recs.flatMap(r=>(r?.rules??[]).map(rr=>rr?.ctor));
  if(ruleIds.some(x=>!Number.isSafeInteger(x))||new Set(ruleIds).size!==ruleIds.length)return false;
  const minors=ruleIds.length,motives=recs.length;
  if(!recs.every(r=>r&&r.numParams===0&&r.numIndices===0&&r.numMotives===motives&&
      r.numMinors===minors&&r.k===false&&r.isUnsafe===false))return false;
  const sourceCtors=new Set((source.ctors??[]));
  const sourceRuleSets=recs.filter(r=>(r.rules??[]).some(rr=>sourceCtors.has(rr.ctor)));
  return sourceRuleSets.length===1 &&
    (sourceRuleSets[0].rules??[]).length===sourceCtors.size &&
    (sourceRuleSets[0].rules??[]).every(rr=>sourceCtors.has(rr.ctor));
}
function rewrite(input){
  const out=[];let rewritten=0;
  for(const line of input.split(/\r?\n/)){
    if(!line.trim())continue;
    const row=JSON.parse(line),b=row.inductive;
    if(!b||!recognizedEnvelope(b)){out.push(line);continue;}
    const source=b.types[0];
    out.push(JSON.stringify({axiom:{name:source.name,levelParams:source.levelParams??[],type:source.type,isUnsafe:false}}));
    for(const c of b.ctors??[])out.push(JSON.stringify({axiom:{name:c.name,levelParams:c.levelParams??[],type:c.type,isUnsafe:false}}));
    for(const r of b.recs??[])out.push(JSON.stringify({axiom:{name:r.name,levelParams:r.levelParams??[],type:r.type,isUnsafe:false}}));
    rewritten++;
  }
  return {text:out.join("\n")+"\n",rewritten};
}
const rows=[];
for(const [name,want] of CASES){
  const input=readFileSync("_build/tests/"+name+".ndjson","utf8"),rw=rewrite(input),t0=Date.now();
  const r=K.checkExport(rw.text,CAPS,1_000_000);
  const pass=want==="either"?(r.status==="ACCEPT"||r.status==="REJECT"):r.status===want;
  const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    parse_records:r.parse_records??null,rewritten:rw.rewritten,elapsed_ms:Date.now()-t0,pass};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const good=rows.slice(0,2),controls=rows.slice(2);
const out={experiment:"validated-nested-axiomization-separator",
  closesGiants:good.every(r=>r.status==="ACCEPT"),controlsClean:controls.every(r=>r.pass),rows,
  claim_boundary:"Consequence-minimal separator only. The two known-good zero-parameter nested bundles have separately passed exact mutual recursor type/rule derivation. This experiment asks whether subsequent Arena checking requires their computation rules at all by replacing that already-validated package with opaque typed constants. It is not a production validator and cannot by itself justify accepting arbitrary nested packages."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/validated-nested-axiomization-separator.json",JSON.stringify(out,null,2)+"\n");
console.log("VALIDATED_NESTED_AXIOMIZATION_SEPARATOR "+JSON.stringify(out));
if(!out.closesGiants||!out.controlsClean)process.exit(1);
