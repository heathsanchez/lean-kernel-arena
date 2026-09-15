import {readFileSync,writeFileSync,mkdirSync} from "node:fs";

const TARGETS=["init-prelude","perf/grind-ring-5"];

function scan(name){
  const data=readFileSync("_build/tests/"+name+".ndjson","utf8");
  const names=new Map([[0,"[]"]]),exprs=new Map();
  const nm=id=>names.get(id)??("#"+id), ex=id=>exprs.get(id);
  let first=null,lineNo=0;
  function head(e){let h=e,args=[];while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {h,args};}
  function stripLams(e){const doms=[];let x=e;while(Array.isArray(x)&&x[0]==="lam"){doms.push(x[1]);x=x[2];}return {doms,body:x};}
  function stripPis(e){const doms=[];let x=e;while(Array.isArray(x)&&x[0]==="pi"){doms.push(x[1]);x=x[2];}return {doms,body:x};}
  function sig(e){
    const {h,args}=head(e);
    if(!Array.isArray(h))return {head:typeof h,args:args.length};
    return {head:h[0]==="const"?h[1]:h[0],args:args.length};
  }
  for(const line of data.split(/\r?\n/)){
    if(!line.trim())continue;lineNo++;const row=JSON.parse(line);
    if(Number.isSafeInteger(row.in)){
      if(row.str&&typeof row.str.str==="string")names.set(row.in,nm(row.str.pre)+"."+row.str.str);
      else if(row.num&&Number.isSafeInteger(row.num.i))names.set(row.in,nm(row.num.pre)+"."+row.num.i);
    }
    if(Number.isSafeInteger(row.ie)){
      let e=null,v;
      if((v=row.sort)!==undefined)e=["sort",v];
      else if((v=row.bvar)!==undefined)e=["var",v];
      else if((v=row.const)!==undefined)e=["const",nm(v.name)];
      else if((v=row.app)!==undefined)e=["app",ex(v.fn),ex(v.arg)];
      else if((v=row.lam)!==undefined)e=["lam",ex(v.type),ex(v.body)];
      else if((v=row.forallE)!==undefined)e=["pi",ex(v.type),ex(v.body)];
      else if((v=row.letE)!==undefined)e=["let",ex(v.type),ex(v.value),ex(v.body)];
      else if((v=row.mdata)!==undefined)e=ex(v.expr);
      else if((v=row.proj)!==undefined)e=["proj",nm(v.typeName),v.idx,ex(v.struct)];
      else if((v=row.natVal)!==undefined)e=["nat",v];
      else if((v=row.strVal)!==undefined)e=["strlit",v];
      if(e)exprs.set(row.ie,e);
    }
    const b=row.inductive;
    if(!b||first||(b.types??[]).every(t=>(t.numNested??0)===0))continue;
    const motives=(b.recs?.[0]?.numMotives??0),minors=(b.recs?.[0]?.numMinors??0);
    const recs=(b.recs??[]).map(r=>{
      const pi=stripPis(ex(r.type));
      const rules=(r.rules??[]).map(rr=>{
        const lam=stripLams(ex(rr.rhs));
        const hb=head(lam.body);
        return {
          ctor:nm(rr.ctor),nfields:rr.nfields,lambdas:lam.doms.length,
          bodyHead:Array.isArray(hb.h)?(hb.h[0]==="var"?["var",hb.h[1]]:[hb.h[0],hb.h[1]??null]):hb.h,
          bodyArgs:hb.args.length
        };
      });
      return {
        name:nm(r.name),motives:r.numMotives,minors:r.numMinors,
        binders:pi.doms.length,
        motiveDomains:pi.doms.slice(0,motives).map(sig),
        minorDomains:pi.doms.slice(motives,motives+minors).map(sig),
        majorDomain:sig(pi.doms.at(-1)),
        result:sig(pi.body),rules
      };
    });
    first={lineNo,motives,minors,recs};
  }
  return {name,first};
}
const results=TARGETS.map(scan);
const out={experiment:"nested-minor-order-diagnostic",results};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/nested-minor-order-diagnostic.json",JSON.stringify(out,null,2)+"\n");
console.log("NESTED_MINOR_ORDER_DIAGNOSTIC "+JSON.stringify(out));
