import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype,sub0=p.substitute,run0=p.run,whnf0=p.whnf,seen=[];

function freeMask(k,root){
  if(!Array.isArray(root))return 0n;
  k.__mask??=new WeakMap();if(k.__mask.has(root))return k.__mask.get(root);
  const work=[{e:root,post:false}],vals=[];
  while(work.length){
    const f=work.pop(),e=f.e;
    if(k.__mask.has(e)){vals.push(k.__mask.get(e));continue;}
    if(f.post){
      const take=()=>vals.pop();let m=0n;
      if(f.tag==="pi"||f.tag==="lam"){const b=take(),a=take();m=a|(b>>1n);}
      else if(f.tag==="app"){const a=take(),fn=take();m=fn|a;}
      else if(f.tag==="proj")m=take();
      else if(f.tag==="let"){const b=take(),v=take(),a=take();m=a|v|(b>>1n);}
      k.__mask.set(e,m);vals.push(m);continue;
    }
    let m;
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":m=0n;break;
      case "var":m=1n<<BigInt(e[1]);break;
      case "pi":case "lam":work.push({e,post:true,tag:e[0]});work.push({e:e[2],post:false});work.push({e:e[1],post:false});continue;
      case "app":work.push({e,post:true,tag:"app"});work.push({e:e[2],post:false});work.push({e:e[1],post:false});continue;
      case "proj":work.push({e,post:true,tag:"proj"});work.push({e:e[3],post:false});continue;
      case "let":work.push({e,post:true,tag:"let"});work.push({e:e[3],post:false});work.push({e:e[2],post:false});work.push({e:e[1],post:false});continue;
      default:m=-1n;
    }
    k.__mask.set(e,m);vals.push(m);
  }
  return vals.pop();
}
function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {h,args};}
function part(k,e){
  const m=freeMask(k,e);
  if(Array.isArray(e)&&e[0]==="var"&&e[1]===0)return "v0";
  if(m===0n)return "closed";
  if((m&1n)===0n)return "drop";
  return "uses";
}
p.run=function(...args){this.__mask=new WeakMap();this.__whnfKind=[];this.__subDepth=0;this.__shapeStats=new Map();seen.push(this);return run0.apply(this,args);};
p.whnf=function(e){this.__whnfKind.push(Array.isArray(e)?e[0]:"p");try{return whnf0.call(this,e);}finally{this.__whnfKind.pop();}};
p.substitute=function(root,arg,depth=0){
  const outer=(this.__subDepth??0)===0;this.__subDepth=(this.__subDepth??0)+1;
  const before=this.steps??0;
  let sig=null;
  if(outer&&depth===0&&this.__whnfKind?.at(-1)==="app"&&(freeMask(this,root)&1n)!==0n){
    const {h,args}=spine(root);
    const ps=args.map(a=>part(this,a));
    sig=JSON.stringify({head:part(this,h),argc:args.length,v0:ps.filter(x=>x==="v0").length,
      closed:ps.filter(x=>x==="closed").length,drop:ps.filter(x=>x==="drop").length,uses:ps.filter(x=>x==="uses").length});
  }
  try{return sub0.call(this,root,arg,depth);}
  finally{
    this.__subDepth--;
    if(sig){
      const cost=(this.steps??0)-before,q=this.__shapeStats.get(sig)??{sig:JSON.parse(sig),calls:0,totalCost:0,maxCost:0};
      q.calls++;q.totalCost+=cost;q.maxCost=Math.max(q.maxCost,cost);this.__shapeStats.set(sig,q);
    }
  }
};
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const t0=Date.now(),r=K.checkExport(input,CAPS,1_000_000);
const shapes=[];for(const k of seen)for(const q of k.__shapeStats?.values()??[])shapes.push({...q,avgCost:q.totalCost/Math.max(1,q.calls)});
shapes.sort((a,b)=>b.totalCost-a.totalCost);
const out={experiment:"shared-beta-spine-shape-census",result:{status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0},shapes:shapes.slice(0,40)};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/shared-beta-spine-shape-census.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_BETA_SPINE_SHAPE_CENSUS "+JSON.stringify(out));
