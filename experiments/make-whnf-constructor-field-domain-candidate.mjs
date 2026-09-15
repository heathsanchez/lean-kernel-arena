import {readFileSync,writeFileSync} from "node:fs";
const p="/tmp/mathgraph-zero-nested/kernel-base.mjs";
let s=readFileSync(p,"utf8");
const old="fieldDomains.push(w[1]); ct=w[2];";
const hits=s.split(old).length-1;
if(hits!==2)throw new Error("expected two constructor field-domain sites, got "+hits);
s=s.split(old).join("fieldDomains.push(this.whnf(w[1])); ct=w[2];");
writeFileSync(p,s);
console.log("WHNF_CONSTRUCTOR_FIELD_DOMAINS_READY "+JSON.stringify({sites:hits}));
