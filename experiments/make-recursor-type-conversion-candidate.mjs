import {readFileSync,writeFileSync} from "node:fs";
const p="/tmp/mathgraph-zero-nested/kernel-base.mjs";
let s=readFileSync(p,"utf8");
const old='if(!this.same(rec.type,derived.recType)) this.reject("recursor-type:"+d.name);';
const neu='if(!this.same(rec.type,derived.recType)) { this.equal(rec.type,derived.recType,[]); }';
if(!s.includes(old))throw new Error("recursor-type patch point missing");
s=s.replace(old,neu);
writeFileSync(p,s);
console.log("RECURSOR_TYPE_CONVERSION_READY");
