import {readFileSync,writeFileSync} from "node:fs";
const p="/tmp/mathgraph-zero-nested/kernel-base.mjs";
let s=readFileSync(p,"utf8");
const old='if(!this.same(rr.rhs,derived.ruleBodies[i])) this.reject("recursor-rule-"+i);';
const neu='if(!this.same(rr.rhs,derived.ruleBodies[i])) { if(!Array.isArray(rr.rhs)||!Array.isArray(derived.ruleBodies[i])||rr.rhs[0]!==derived.ruleBodies[i][0]) this.reject("recursor-rule-"+i); this.__recRuleConversionAttempts=(this.__recRuleConversionAttempts??0)+1; this.equal(rr.rhs,derived.ruleBodies[i],[]); this.__recRuleConversionSuccesses=(this.__recRuleConversionSuccesses??0)+1; }';
if(!s.includes(old))throw new Error("recursor-rule patch point missing");
s=s.replace(old,neu);
writeFileSync(p,s);
console.log("RECURSOR_RULE_CONVERSION_READY");
