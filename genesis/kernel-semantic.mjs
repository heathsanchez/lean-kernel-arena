import * as Base from "./kernel-base.mjs";
import {appendName,ROOT as ROOT_NAME} from "./name-codec.mjs";

const {
  levelsEqual,levelSucc,levelIMax,quotientType,Stop,Kernel,
  ACCEPT,REJECT,UNKNOWN,S,V,Pi,Lam,App,Let,NatLit,StrLit,Proj
}=Base;

function unresolvedPropProjectionObstruction(input) {
  try {
    const names=new Map([[0,ROOT_NAME]]),levels=new Map([[0,0]]),exprs=new Map();
    const declTypes=new Map(),forbidden=new Set(),tainted=new Set();
    let header=false,parsed=0,unresolved=false;
    const get=(m,n)=>m.has(n)?m.get(n):null;
    const key=(name,idx)=>`${name}\u0000${idx}`;
    const definitelyPositive=u=>{
      if(typeof u==="number") return u>0;
      if(!Array.isArray(u)) return false;
      if(u[0]==="succ") return true;
      if(u[0]==="max") return definitelyPositive(u[1])||definitelyPositive(u[2]);
      if(u[0]==="imax") return definitelyPositive(u[2]);
      return false;
    };
    const exprTainted=id=>tainted.has(id);
    for(const line of input.split(/\r?\n/)) {
      if(!line.trim()) continue;
      parsed++;
      const row=JSON.parse(line);
      if(!row||Array.isArray(row)||typeof row!=="object") return null;
      const keys=Object.keys(row);
      if(!header) {
        if(keys.length!==1||keys[0]!=="meta"||row.meta?.format?.version!=="3.1.0") return null;
        header=true; continue;
      }
      const refs=keys.filter(k=>["in","il","ie"].includes(k));
      const tags=keys.filter(k=>!["in","il","ie"].includes(k));
      if(tags.length!==1||refs.length>1) return null;
      const tag=tags[0],v=row[tag];
      if(refs[0]==="in") {
        if(names.has(row.in)) return null;
        if(tag==="str"&&v&&typeof v.str==="string") {
          const pre=get(names,v.pre); if(pre===null) return null;
          names.set(row.in,appendName(pre,"str",v.str));
        } else if(tag==="num"&&v&&Number.isSafeInteger(v.i)&&v.i>=0) {
          const pre=get(names,v.pre); if(pre===null) return null;
          names.set(row.in,appendName(pre,"num",v.i));
        } else return null;
        continue;
      }
      if(refs[0]==="il") {
        if(levels.has(row.il)) return null;
        if(tag==="succ") {
          const a=get(levels,v); if(a===null) return null;
          levels.set(row.il,typeof a==="number"?a+1:["succ",a]);
        } else if((tag==="max"||tag==="imax")&&Array.isArray(v)&&v.length===2) {
          const a=get(levels,v[0]),b=get(levels,v[1]); if(a===null||b===null) return null;
          levels.set(row.il,typeof a==="number"&&typeof b==="number"
            ?(tag==="imax"&&b===0?0:Math.max(a,b)):[tag,a,b]);
        } else if(tag==="param") {
          const n=get(names,v); if(n===null) return null;
          levels.set(row.il,["param",n]);
        } else return null;
        continue;
      }
      if(refs[0]==="ie") {
        if(exprs.has(row.ie)) return null;
        let e=null,t=false;
        if(tag==="sort") { const u=get(levels,v); if(u===null) return null; e=["sort",u]; }
        else if(tag==="bvar"&&Number.isSafeInteger(v)&&v>=0) e=["var",v];
        else if(tag==="const"&&v&&Array.isArray(v.us)) {
          const n=get(names,v.name); if(n===null) return null;
          const us=[]; for(const id of v.us) { const u=get(levels,id); if(u===null) return null; us.push(u); }
          e=us.length?["const",n,us]:["const",n];
        } else if((tag==="lam"||tag==="forallE")&&v) {
          const a=get(exprs,v.type),b=get(exprs,v.body); if(a===null||b===null) return null;
          e=[tag==="lam"?"lam":"pi",a,b]; t=exprTainted(v.type)||exprTainted(v.body);
        } else if(tag==="app"&&v) {
          const f=get(exprs,v.fn),a=get(exprs,v.arg); if(f===null||a===null) return null;
          e=["app",f,a]; t=exprTainted(v.fn)||exprTainted(v.arg);
        } else if(tag==="letE"&&v&&typeof v.nondep==="boolean") {
          const a=get(exprs,v.type),x=get(exprs,v.value),b=get(exprs,v.body);
          if(a===null||x===null||b===null) return null;
          e=["let",a,x,b]; t=exprTainted(v.type)||exprTainted(v.value)||exprTainted(v.body);
        } else if(tag==="mdata"&&v) {
          e=get(exprs,v.expr); if(e===null) return null; t=exprTainted(v.expr);
        } else if(tag==="natVal"&&typeof v==="string"&&/^[0-9]+$/.test(v)) e=["nat",v];
        else if(tag==="strVal"&&typeof v==="string") e=["strlit",v];
        else if(tag==="proj"&&v&&Number.isSafeInteger(v.idx)&&v.idx>=0) {
          const n=get(names,v.typeName),s=get(exprs,v.struct); if(n===null||s===null) return null;
          e=["proj",n,v.idx,s]; t=exprTainted(v.struct)||forbidden.has(key(n,v.idx));
        } else return null;
        exprs.set(row.ie,e); if(t) tainted.add(row.ie);
        continue;
      }
      if(tag==="inductive") {
        if(!v||!Array.isArray(v.types)||!Array.isArray(v.ctors)||!Array.isArray(v.recs)) return null;
        for(const it of v.types) {
          if(!it||!Number.isSafeInteger(it.name)||!Number.isSafeInteger(it.type)) return null;
          const n=get(names,it.name),ty=get(exprs,it.type); if(n===null||ty===null) return null;
          declTypes.set(n,ty);
        }
        if(v.types.length===1) continue;
        unresolved=true;
        const ctorsByInd=new Map(v.types.map(it=>[it.name,[]]));
        for(const c of v.ctors) {
          if(!c||!Number.isSafeInteger(c.induct)) return null;
          if(!ctorsByInd.has(c.induct)) continue;
          ctorsByInd.get(c.induct).push(c);
        }
        for(const it of v.types) {
          if(it.numParams!==0||it.numIndices!==0||it.numNested!==0||it.isUnsafe!==false||
             it.isRec!==false||!Array.isArray(it.levelParams)||it.levelParams.length!==0||
             !Array.isArray(it.ctors)||it.ctors.length!==1) continue;
          const tn=get(names,it.name),ty=get(exprs,it.type),cs=ctorsByInd.get(it.name)??[];
          if(tn===null||!ty||ty[0]!=="sort"||ty[1]!==0||cs.length!==1) continue;
          const c=cs[0];
          if(c.name!==it.ctors[0]||c.cidx!==0||c.numParams!==0||c.isUnsafe!==false||
             !Array.isArray(c.levelParams)||c.levelParams.length!==0||
             !Number.isSafeInteger(c.numFields)||c.numFields<0) continue;
          let ct=get(exprs,c.type); if(!ct) continue;
          const fields=[];
          while(ct?.[0]==="pi") { fields.push(ct[1]); ct=ct[2]; }
          if(fields.length!==c.numFields||ct?.[0]!=="const"||ct[1]!==tn||(ct[2]?.length??0)!==0) continue;
          for(let i=0;i<fields.length;i++) {
            const ft=fields[i];
            if(ft?.[0]!=="const"||(ft[2]?.length??0)!==0) continue;
            const fty=declTypes.get(ft[1]);
            if(fty?.[0]==="sort"&&definitelyPositive(fty[1])) forbidden.add(key(tn,i));
          }
        }
        continue;
      }
      if(["axiom","def","opaque","thm"].includes(tag)) {
        if(!v||!Number.isSafeInteger(v.name)||!Number.isSafeInteger(v.type)) return null;
        const n=get(names,v.name),ty=get(exprs,v.type); if(n===null||ty===null) return null;
        declTypes.set(n,ty);
        const used=exprTainted(v.type)||(["def","opaque","thm"].includes(tag)&&exprTainted(v.value));
        if(unresolved&&used&&forbidden.size) return {parsed,declaration:n};
        continue;
      }
      // Quotient records do not create a direct positive-universe field fact needed here.
      if(tag==="quot") continue;
      return null;
    }
    return null;
  } catch {
    return null;
  }
}

function checkExport(input,capabilities,budget=200000) {
  const base=Base.checkExport(input,capabilities,budget);
  if(base.status!==UNKNOWN||base.reason!=="inductive-semantics-frontier"||
     !capabilities.includes("projections")||!capabilities.includes("prop-inductives")) return base;
  const obstruction=unresolvedPropProjectionObstruction(input);
  if(!obstruction) return base;
  const {frontier_inductive,...rest}=base;
  return {...rest,status:REJECT,reason:"projection-data-from-prop",
    parse_records:obstruction.parsed,frontier_declaration:obstruction.declaration};
}

export {levelsEqual,levelSucc,levelIMax,quotientType,Stop,Kernel,ACCEPT,REJECT,UNKNOWN,S,V,Pi,Lam,App,Let,NatLit,StrLit,Proj,checkExport};
