import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
const K=await import("file:///tmp/mathgraph-zero-nested/kernel.mjs");
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function recognizedEnvelope(b){
 const source=(b.types??[]).length===1?b.types[0]:null;
 if(!source||source.numParams!==0||source.numIndices!==0||source.isUnsafe!==false||
    !Array.isArray(source.levelParams)||source.levelParams.length!==0||
    !Number.isSafeInteger(source.numNested)||source.numNested<=0)return false;
 const recs=b.recs??[],ruleIds=recs.flatMap(r=>(r?.rules??[]).map(rr=>rr?.ctor));
 if(recs.length!==1+source.numNested||new Set(ruleIds).size!==ruleIds.length)return false;
 return recs.every(r=>r&&r.numParams===0&&r.numIndices===0&&r.numMotives===recs.length&&
   r.numMinors===ruleIds.length&&r.k===false&&r.isUnsafe===false);
}
function rewrite(input){
 const out=[];let rewritten=0;
 for(const line of input.split(/\r?\n/)){
  if(!line.trim())continue;const row=JSON.parse(line),b=row.inductive;
  if(!b||!recognizedEnvelope(b)){out.push(line);continue;}
  const source=b.types[0];
  out.push(JSON.stringify({axiom:{name:source.name,levelParams:source.levelParams??[],type:source.type,isUnsafe:false}}));
  for(const c of b.ctors??[])out.push(JSON.stringify({axiom:{name:c.name,levelParams:c.levelParams??[],type:c.type,isUnsafe:false}}));
  for(const r of b.recs??[])out.push(JSON.stringify({axiom:{name:r.name,levelParams:r.levelParams??[],type:r.type,isUnsafe:false}}));
  rewritten++;
 }
 return {text:out.join("\n")+"\n",rewritten};
}
const CASES=[
 ["init-prelude","ACCEPT",true],
 ["perf/grind-ring-5","ACCEPT",true],
 ["tutorial/101_natLitEq","ACCEPT",false],
 ["nested-unused-param","REJECT",false],
 ["nested-nonuniform-param","either",false]
];
const rows=[];
for(const [name,want,doRewrite] of CASES){
 const input=readFileSync("_build/tests/"+name+".ndjson","utf8"),rw=doRewrite?rewrite(input):{text:input,rewritten:0},t0=Date.now();
 const r=K.checkExport(rw.text,CAPS,1_000_000);
 const pass=want==="either"?(r.status==="ACCEPT"||r.status==="REJECT"):r.status===want;
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
  parse_records:r.parse_records??null,frontier_declaration:r.frontier_declaration??null,
  conversion_frontier:r.conversion_frontier??null,rewritten:rw.rewritten,elapsed_ms:Date.now()-t0,pass};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const protectedClean=rows.slice(2).every(r=>r.pass),initAdvanced=rows[0].reason!=="nat-literal-budget";
const out={experiment:"arbitrary-nat-after-nested",initAdvanced,protectedClean,rows,
 claim_boundary:"Primitive-natural representation experiment. Safe naturals retain the existing numeric representation; oversized decimal natVal atoms use a canonical decimal string, are typed as Nat, and use exact BigInt predecessor only if WHNF reduction is demanded. Nested good bundles are consequence-separator axiomized exactly as in the prior experiment. Promotion requires independent package validation and broad replay."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/arbitrary-nat-after-nested.json",JSON.stringify(out,null,2)+"\n");
console.log("ARBITRARY_NAT_AFTER_NESTED "+JSON.stringify(out));
if(!initAdvanced||!protectedClean)process.exit(1);
