import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype,sub0=p.substitute,run0=p.run,seen=[];

function mask(k,e){
  if(!Array.isArray(e))return 0n;
  k.__posMask??=new WeakMap();
  const old=k.__posMask.get(e);if(old!==undefined)return old;
  let m;
  switch(e[0]){
    case "sort":case "const":case "nat":case "strlit":m=0n;break;
    case "var":m=1n<<BigInt(e[1]);break;
    case "app":m=mask(k,e[1])|mask(k,e[2]);break;
    case "proj":m=mask(k,e[3]);break;
    case "pi":case "lam":m=mask(k,e[1])|(mask(k,e[2])>>1n);break;
    case "let":m=mask(k,e[1])|mask(k,e[2])|(mask(k,e[3])>>1n);break;
    default:m=-1n;
  }
  k.__posMask.set(e,m);return m;
}
function spine(e){const a=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){a.push(h[2]);h=h[1];}a.reverse();return{h,a};}
function nodes(e){if(!Array.isArray(e))return 0;let n=1;for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))n+=nodes(e[i]);return n;}

p.run=function(...xs){this.__posMask=new WeakMap();this.__posDepth=0;this.__posRows=new Map();seen.push(this);return run0.apply(this,xs);};
p.substitute=function(root,arg,depth=0){
  const outer=(this.__posDepth??0)===0;this.__posDepth=(this.__posDepth??0)+1;
  let key=null,before=0;
  if(outer&&depth===0&&Array.isArray(root)){
    const {h,a}=spine(root);
    if(a.length===5&&mask(this,h)===0n){
      const kinds=a.map(x=>{const m=mask(this,x);return m===0n?"C":(m&1n)!==0n?"D":"U";});
      if(kinds.filter(x=>x==="D").length===1&&kinds.filter(x=>x==="C").length===4){
        const pos=kinds.indexOf("D");
        key=JSON.stringify({pos,headTag:h?.[0],dynamicTag:a[pos]?.[0],
          dynamicNodes:nodes(a[pos]),closedNodes:a.map((x,i)=>i===pos?0:nodes(x)).reduce((x,y)=>x+y,0)});
        before=this.steps??0;
      }
    }
  }
  try{return sub0.call(this,root,arg,depth);}
  finally{
    this.__posDepth--;
    if(key){
      const cost=(this.steps??0)-before,q=this.__posRows.get(key)??{...JSON.parse(key),calls:0,totalCost:0,maxCost:0};
      q.calls++;q.totalCost+=cost;q.maxCost=Math.max(q.maxCost,cost);this.__posRows.set(key,q);
    }
  }
};

const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const t0=Date.now(),r=K.checkExport(input,CAPS,1_000_000),rows=[];
for(const k of seen)for(const q of k.__posRows?.values()??[])rows.push({...q,avgCost:q.totalCost/Math.max(1,q.calls)});
rows.sort((a,b)=>b.totalCost-a.totalCost);
const byPosition={};
for(const q of rows){const z=byPosition[q.pos]??={calls:0,totalCost:0};z.calls+=q.calls;z.totalCost+=q.totalCost;byPosition[q.pos]=z;}
const out={experiment:"shared-beta-dynamic-position-census",
 result:{status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0},
 byPosition,top:rows.slice(0,30)};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/shared-beta-dynamic-position-census.json",import.meta.url),JSON.stringify(out,null,2)+"\n");
console.log("SHARED_BETA_DYNAMIC_POSITION_CENSUS "+JSON.stringify(out));
