import {readFileSync} from "node:fs";
import * as K from "../genesis/kernel.mjs";

const [dumpPath]=process.argv.slice(2);
if(!dumpPath) throw new Error("usage: node con-leche-model-missing-const-v4.mjs DUMP");
const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const dump=readFileSync(dumpPath,"utf8");

let strippedBlocks=0,canonicalizedFieldlessRecFlags=0;
const out=[];
for(const line of dump.split(/\r?\n/)){
  if(!line.trim()) continue;
  const r=JSON.parse(line);
  if(r.inductive){
    const ts=r.inductive.types??[],cs=r.inductive.ctors??[];
    if(ts.length>1||ts.some(t=>(t?.numNested??0)>0)){strippedBlocks++;continue;}
    if(ts.length===1 && cs.every(c=>(c?.numFields??-1)===0) && ts[0].isRec===true){
      ts[0].isRec=false; canonicalizedFieldlessRecFlags++;
    }
  }
  out.push(JSON.stringify(r));
}
const compiled=out.join("\n")+"\n";

const misses=[];
const origInfer=K.Kernel.prototype.infer;
K.Kernel.prototype.infer=function(e,ctx){
  if(Array.isArray(e)&&e[0]==="const"&&!this.env.has(e[1]))
    misses.push({op:"infer",missing:e[1],currentDeclaration:this.currentDeclaration??null,ctxDepth:ctx?.length??null});
  return origInfer.call(this,e,ctx);
};
const origWhnf=K.Kernel.prototype.whnf;
K.Kernel.prototype.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="const"&&!this.env.has(e[1]))
    misses.push({op:"whnf",missing:e[1],currentDeclaration:this.currentDeclaration??null});
  return origWhnf.call(this,e);
};

const result=K.checkExport(compiled,caps,4_000_000);
console.log("CON_LECHE_MODEL_MISSING_CONST_V4 "+JSON.stringify({
  strippedBlocks,canonicalizedFieldlessRecFlags,
  status:result.status,reason:result.reason,steps:result.steps??null,
  frontier_declaration:result.frontier_declaration??null,
  misses:misses.slice(-20)
}));
