import {readFileSync} from "node:fs";

const TARGETS=["init-prelude","perf/grind-ring-5"];

function nameText(names,id){
  return names.get(id)??("#"+String(id));
}
function scan(name){
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const lines=input.split(/\r?\n/);
  const names=new Map([[0,""]]);
  const mismatches=[];
  for(let i=0;i<lines.length;i++){
    const line=lines[i];
    if(!line.trim()) continue;
    const row=JSON.parse(line);
    const keys=Object.keys(row);
    const refs=keys.filter(k=>["in","il","ie"].includes(k));
    const tags=keys.filter(k=>!["in","il","ie"].includes(k));
    const tag=tags[0],v=row[tag];
    if(refs[0]==="in"){
      if(tag==="str"&&v&&typeof v.str==="string"){
        const pre=names.get(v.pre);
        if(pre!==undefined) names.set(row.in,pre?pre+"."+v.str:v.str);
      }else if(tag==="num"&&v&&Number.isSafeInteger(v.i)){
        const pre=names.get(v.pre);
        if(pre!==undefined) names.set(row.in,pre?pre+"."+v.i:String(v.i));
      }
      continue;
    }
    if(tag!=="inductive") continue;
    const summary={
      file:name,record:i+1,
      typeCount:Array.isArray(v?.types)?v.types.length:null,
      ctorCount:Array.isArray(v?.ctors)?v.ctors.length:null,
      recCount:Array.isArray(v?.recs)?v.recs.length:null,
      types:(v?.types??[]).map((x,j)=>({
        j,name:nameText(names,x?.name),nameId:x?.name,
        numParams:x?.numParams,numIndices:x?.numIndices,numNested:x?.numNested,
        isRec:x?.isRec,isUnsafe:x?.isUnsafe,isReflexive:x?.isReflexive,
        all:(x?.all??[]).map(n=>nameText(names,n)),
        ctors:(x?.ctors??[]).map(n=>nameText(names,n))
      })),
      ctors:(v?.ctors??[]).map((x,j)=>({
        j,name:nameText(names,x?.name),induct:nameText(names,x?.induct),
        cidx:x?.cidx,numParams:x?.numParams,numFields:x?.numFields,isUnsafe:x?.isUnsafe
      })),
      recs:(v?.recs??[]).map((x,j)=>({
        j,name:nameText(names,x?.name),numParams:x?.numParams,numIndices:x?.numIndices,
        numMotives:x?.numMotives,numMinors:x?.numMinors,k:x?.k,isUnsafe:x?.isUnsafe,
        rules:(x?.rules??[]).map(r=>({ctor:nameText(names,r?.ctor),nfields:r?.nfields}))
      }))
    };
    if(summary.recCount!==summary.typeCount) mismatches.push(summary);
  }
  console.log("GIANT_INDUCTIVE_MISMATCH "+JSON.stringify({file:name,count:mismatches.length,first:mismatches.slice(0,8)}));
}
for(const t of TARGETS) scan(t);
