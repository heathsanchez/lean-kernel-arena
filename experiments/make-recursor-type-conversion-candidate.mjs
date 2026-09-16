import {readFileSync,writeFileSync} from "node:fs";
const p="/tmp/mathgraph-zero-nested/kernel-base.mjs";
let s=readFileSync(p,"utf8");
const old='if(!this.same(rec.type,derived.recType)) this.reject("recursor-type:"+d.name);';
const neu='if(!this.same(rec.type,derived.recType)) { if(!Array.isArray(rec.type)||!Array.isArray(derived.recType)||rec.type[0]!==derived.recType[0]) this.reject("recursor-type:"+d.name); this.__recTypeConversionAttempts=(this.__recTypeConversionAttempts??0)+1; this.equal(rec.type,derived.recType,[]); this.__recTypeConversionSuccesses=(this.__recTypeConversionSuccesses??0)+1; }';
if(!s.includes(old))throw new Error("recursor-type patch point missing");
s=s.replace(old,neu);
writeFileSync(p,s);
console.log("RECURSOR_TYPE_CONVERSION_READY");
