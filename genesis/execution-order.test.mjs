import test from "node:test";
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {checkExport as kernelCheckExport} from "./kernel.mjs";
import {CAPABILITIES,checkExport,productionConfig} from "./production.mjs";

function deepExport(depth=600,bad=false) {
  const rows=[{meta:{format:{version:"3.1.0"}}},
    {in:1,str:{pre:0,str:"P"}},{in:2,str:{pre:0,str:"p"}},{in:3,str:{pre:0,str:"deep"}},
    {ie:0,sort:0},{ie:1,const:{name:1,us:[]}},{ie:2,const:{name:2,us:[]}},
    {axiom:{name:1,type:0,levelParams:[],isUnsafe:false}},
    {axiom:{name:2,type:1,levelParams:[],isUnsafe:false}},
    {ie:3,bvar:0},{ie:4,lam:{type:1,body:3,binderInfo:"default"}}];
  let value=2,next=5;
  for(let i=0;i<depth;i++) { rows.push({ie:next,app:{fn:4,arg:value}});value=next++; }
  rows.push({def:{name:3,type:bad?0:1,value,levelParams:[],safety:"safe",all:[3],hints:{regular:0}}});
  return rows.map(JSON.stringify).join("\n");
}

test("deep app/lambda terms use the continuation evaluator first",()=>{
  const result=checkExport(deepExport());
  assert.equal(result.status,"ACCEPT");
  assert.equal(result.execution_order,"local-def-first");
  assert.ok(result.max_expression_depth>512);
  assert.equal(result.fallback_mode,undefined);
});

test("deep routing preserves false typing rejection",()=>{
  const result=checkExport(deepExport(600,true));
  assert.equal(result.status,"REJECT");
  assert.equal(result.execution_order,"local-def-first");
});

test("deep UNKNOWN retains both attempt budgets and evidence",()=>{
  const config={...productionConfig(),semanticBudget:1};
  const result=checkExport(deepExport(),config);
  assert.equal(result.status,"UNKNOWN");
  assert.equal(result.reason,"budget-exhausted");
  assert.equal(result.steps,2);
  assert.equal(result.first_attempt_reason,"budget-exhausted");
  assert.equal(result.first_attempt_steps,2);
  assert.equal(result.execution_order,"local-def-first");
});

test("shallow exports retain the ordinary execution path",()=>{
  const input=readFileSync(new URL("../tests/sparse-name-index.ndjson",import.meta.url),"utf8");
  const routed=checkExport(input),ordinary=kernelCheckExport(input,CAPABILITIES,productionConfig().semanticBudget);
  assert.equal(routed.status,ordinary.status);
  assert.equal(routed.reason,ordinary.reason);
  assert.equal(routed.execution_order,undefined);
});
