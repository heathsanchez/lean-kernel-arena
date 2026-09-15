import {readFileSync,writeFileSync} from "node:fs";
const p="/tmp/mathgraph-zero-nested/kernel-base.mjs";
let s=readFileSync(p,"utf8");

const parseOld=`const n=Number(v);
          if(!Number.isSafeInteger(n)) fail("nat-literal-budget");
          e=NatLit(n);`;
const parseNew=`const n=Number(v);
          const canon=v.replace(/^0+(?=[0-9])/,"");
          e=NatLit(Number.isSafeInteger(n)?n:canon);`;
if(!s.includes(parseOld))throw new Error("nat parser patch point missing");
s=s.replace(parseOld,parseNew);

const validOld=`if(!Number.isSafeInteger(e[1])||e[1]<0) this.reject("malformed-nat-literal");`;
const validNew=`if(!((Number.isSafeInteger(e[1])&&e[1]>=0)||
         (typeof e[1]==="string"&&/^(0|[1-9][0-9]*)$/.test(e[1]))))
        this.reject("malformed-nat-literal");`;
if(!s.includes(validOld))throw new Error("nat validation patch point missing");
s=s.replace(validOld,validNew);

const whnfOld=`return e[1]===0?zero:this.make("app",succ,this.make("nat",e[1]-1));`;
const whnfNew=`if(e[1]===0||e[1]==="0") return zero;
      const pred=typeof e[1]==="number"?e[1]-1:(BigInt(e[1])-1n).toString();
      return this.make("app",succ,this.make("nat",pred));`;
if(!s.includes(whnfOld))throw new Error("nat whnf patch point missing");
s=s.replace(whnfOld,whnfNew);

writeFileSync(p,s);
console.log("ARBITRARY_NAT_CANDIDATE_READY");
