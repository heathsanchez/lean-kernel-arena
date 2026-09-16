import {readFileSync} from "node:fs";
import {checkExport,productionConfig} from "./production.mjs";

const targets=["init-prelude","perf/grind-ring-5"];
const config=productionConfig({...process.env,MATHGRAPH_SEMANTIC_BUDGET:"2000000",MATHGRAPH_INPUT_BYTE_LIMIT:"20000000",MATHGRAPH_RECORD_LIMIT:"400000"});

for(const name of targets){
  const input=readFileSync(new URL(`../_build/tests/${name}.ndjson`,import.meta.url),"utf8");
  const result=checkExport(input,config);
  console.log("GIANT_HOST_STACK_TRACE "+JSON.stringify({
    name,status:result.status,reason:result.reason,steps:result.steps??null,
    frontier:result.frontier_declaration??null,
    execution_order:result.execution_order??"retained-first",
    max_expression_depth:result.max_expression_depth??null,
    first_attempt_reason:result.first_attempt_reason??null,
    first_attempt_steps:result.first_attempt_steps??null,
    fallback_mode:result.fallback_mode??null,
    retained_reason:result.retained_reason??null,
    retained_steps:result.retained_steps??null,
    stack_attempt_reason:result.stack_attempt_reason??null,
    stack_attempt_steps:result.stack_attempt_steps??null,
    fallback_attempt_reason:result.fallback_attempt_reason??null,
    fallback_attempt_steps:result.fallback_attempt_steps??null,
    diagnostic_error:result.diagnostic_error??null,
    conversion_frontier:result.conversion_frontier??null
  }));
}
