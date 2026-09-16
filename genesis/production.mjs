import {checkExport as kernelCheckExport} from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./support-metadata-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./compiled-nat-pow-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";

const CAPABILITIES=Object.freeze(["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"]);
const PRODUCTION_DEFAULTS=Object.freeze({semanticBudget:2_000_000,inputBytes:20_000_000,recordLimit:400_000});
const PRODUCTION_ENV=Object.freeze({semanticBudget:"MATHGRAPH_SEMANTIC_BUDGET",inputBytes:"MATHGRAPH_INPUT_BYTE_LIMIT",recordLimit:"MATHGRAPH_RECORD_LIMIT"});
function productionConfig(env=process.env) {
  const out={};
  for(const key of Object.keys(PRODUCTION_DEFAULTS)) {
    const value=Number(env?.[PRODUCTION_ENV[key]]);
    out[key]=Number.isSafeInteger(value)&&value>0?value:PRODUCTION_DEFAULTS[key];
  }
  return out;
}
function checkExport(input,config=productionConfig()) {
  const prior={};
  for(const key of ["inputBytes","recordLimit"]) {
    const name=PRODUCTION_ENV[key];prior[name]=process.env[name];process.env[name]=String(config[key]);
  }
  try { return kernelCheckExport(input,CAPABILITIES,config.semanticBudget); }
  finally {
    for(const [name,value] of Object.entries(prior)) value===undefined?delete process.env[name]:process.env[name]=value;
  }
}

export {CAPABILITIES,PRODUCTION_DEFAULTS,PRODUCTION_ENV,productionConfig,checkExport};
