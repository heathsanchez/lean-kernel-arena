import {cpSync,readFileSync,rmSync,writeFileSync} from "node:fs";
import {fileURLToPath} from "node:url";

const dst="/tmp/mathgraph-zero-nested";
rmSync(dst,{recursive:true,force:true});
cpSync(fileURLToPath(new URL("../genesis/",import.meta.url)),dst,{recursive:true});

const p=dst+"/kernel-base.mjs";
let s=readFileSync(p,"utf8");
s=s.replace("input.length>2000000","input.length>16000000");
s=s.replace("++parsed>100000","++parsed>300000");

const old='if(v.recs.length!==v.types.length) reject("inductive-recursor-count");';
const replacement=`const nestedRuleCtors=new Set(v.recs.flatMap(r=>(r?.rules??[]).map(rr=>rr?.ctor)));
        const source=v.types.length===1?v.types[0]:null;
        const zeroNestedEnvelope=!!source &&
          source.numParams===0 && source.numIndices===0 && source.isUnsafe===false &&
          Number.isSafeInteger(source.numNested) && source.numNested>0 &&
          v.recs.length===1+source.numNested &&
          v.recs.every(r=>r && r.numMotives===1+source.numNested &&
            r.numMinors===nestedRuleCtors.size);
        if(!zeroNestedEnvelope && v.recs.length!==v.types.length) reject("inductive-recursor-count");`;
if(!s.includes(old))throw new Error("recursor-count patch point missing");
s=s.replace(old,replacement);

const oldMinor='if(rec.numMinors!==v.ctors.length) reject("inductive-minor-count");';
const newMinor='if(!zeroNestedEnvelope && rec.numMinors!==v.ctors.length) reject("inductive-minor-count");';
if(!s.includes(oldMinor))throw new Error("minor-count patch point missing");
s=s.replace(oldMinor,newMinor);
writeFileSync(p,s);
console.log("ZERO_PARAM_NESTED_PARSER_CANDIDATE_READY");
