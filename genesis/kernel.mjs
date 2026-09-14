// Experimental monomorphic Lean fragment. No claim of complete Lean soundness.
// The host supplies parsing, budgets and candidate rules; retained capabilities start empty.
const ACCEPT = "ACCEPT", REJECT = "REJECT", UNKNOWN = "UNKNOWN";
const S = n => ["sort", n], V = n => ["var", n];
const Pi = (a,b) => ["pi",a,b], Lam = (a,b) => ["lam",a,b];
const App = (f,a) => ["app",f,a], Let = (a,v,b) => ["let",a,v,b];
class Stop extends Error { constructor(status, reason) { super(reason); this.status=status; } }
class Kernel {
  constructor(capabilities=[], budget=50000) {
    this.caps=new Set(capabilities); this.budget=budget;
  }
  run(term, expected, declarations=[]) {
    this.steps=0; this.env=new Map(); this.allocations=0;
    const start=Date.now();
    try {
      if (!this.caps.size) this.unknown("empty-present");
      this.validate(term); this.validate(expected);
      if (declarations.length) this.need("declarations");
      for (const d of declarations) {
        this.tick();
        if (!d || typeof d.name!=="string" || !["axiom","def"].includes(d.kind)) this.unknown("declaration-kind");
        if (this.env.has(d.name)) this.reject("duplicate-declaration");
        this.validate(d.type);
        this.sortOf(d.type,[]);
        if (d.kind==="def") {
          this.validate(d.value);
          this.equal(this.infer(d.value,[]),d.type);
        }
        // Install only after validation; self and forward references cannot be used.
        this.env.set(d.name,d);
      }
      if ((this.caps.has("sort-direct") || this.caps.has("sort")) && term[0]==="sort" && expected[0]==="sort") {
        if(term[1]+1!==expected[1]) this.reject("sort-mismatch");
      } else {
        this.sortOf(expected,[]);
        this.equal(this.infer(term,[]),expected);
      }
      return this.result(ACCEPT,"obligations-discharged",start);
    } catch(e) {
      if(e instanceof Stop) return this.result(e.status,e.message,start);
      if(e instanceof RangeError) return this.result(UNKNOWN,"host-stack-limit",start);
      throw e; // A programming exception is never converted into proof rejection.
    }
  }
  result(status,reason,start) { return {status,reason,steps:this.steps,constructed:this.allocations,elapsed_ms:Date.now()-start}; }
  tick() { if(++this.steps>this.budget) this.unknown("budget-exhausted"); }
  need(c) { if(!this.caps.has(c)) this.unknown("missing:"+c); }
  unknown(r) { throw new Stop(UNKNOWN,r); }
  reject(r) { throw new Stop(REJECT,r); }
  make(...xs) { this.tick(); this.allocations++; return xs; }
  validate(e) {
    this.tick();
    if(!Array.isArray(e) || typeof e[0]!=="string") this.reject("malformed-term");
    const arities={sort:2,var:2,const:2,pi:3,lam:3,app:3,let:4};
    if(!(e[0] in arities)) this.unknown("syntax:"+e[0]);
    if(e.length!==arities[e[0]]) this.reject("malformed-arity");
    if(e[0]==="sort" || e[0]==="var") {
      if(!Number.isSafeInteger(e[1]) || e[1]<0) this.reject("malformed-index");
      if(e[1]>1000000) this.unknown("index-limit");
    } else if(e[0]==="const") {
      if(typeof e[1]!=="string") this.reject("malformed-name");
    } else for(let i=1;i<e.length;i++) this.validate(e[i]);
  }
  shift(e,amount,cut=0) {
    this.tick();
    switch(e[0]) {
      case "sort": case "const": return e;
      case "var": return e[1]<cut ? e : this.make("var",e[1]+amount);
      case "pi": case "lam": return this.make(e[0],this.shift(e[1],amount,cut),this.shift(e[2],amount,cut+1));
      case "app": return this.make("app",this.shift(e[1],amount,cut),this.shift(e[2],amount,cut));
      case "let": return this.make("let",this.shift(e[1],amount,cut),this.shift(e[2],amount,cut),this.shift(e[3],amount,cut+1));
      default: this.unknown("shift-syntax");
    }
  }
  substitute(e,arg,depth=0) {
    this.tick();
    switch(e[0]) {
      case "sort": case "const": return e;
      case "var": return e[1]===depth ? this.shift(arg,depth) : e[1]>depth ? this.make("var",e[1]-1) : e;
      case "pi": case "lam": return this.make(e[0],this.substitute(e[1],arg,depth),this.substitute(e[2],arg,depth+1));
      case "app": return this.make("app",this.substitute(e[1],arg,depth),this.substitute(e[2],arg,depth));
      case "let": return this.make("let",this.substitute(e[1],arg,depth),this.substitute(e[2],arg,depth),this.substitute(e[3],arg,depth+1));
      default: this.unknown("substitution-syntax");
    }
  }
  whnf(e) {
    this.tick();
    if(e[0]==="const") {
      this.need("declarations");
      const d=this.env.get(e[1]);
      if(!d) this.reject("undeclared-constant");
      if(d.kind==="def") {this.need("reduction"); return this.whnf(d.value);}
    }
    if(e[0]==="let") {this.need("reduction");return this.whnf(this.substitute(e[3],e[2]));}
    if(e[0]==="app") {
      this.need("application");
      const f=this.whnf(e[1]);
      if(f[0]==="lam") {this.need("reduction");return this.whnf(this.substitute(f[2],e[2]));}
      return f===e[1] ? e : this.make("app",f,e[2]);
    }
    return e;
  }
  same(a,b) {
    this.tick();
    if(a===b) return true;
    if(a.length!==b.length || a[0]!==b[0]) return false;
    for(let i=1;i<a.length;i++) {
      if(Array.isArray(a[i])) {if(!Array.isArray(b[i]) || !this.same(a[i],b[i])) return false;}
      else if(a[i]!==b[i]) return false;
    }
    return true;
  }
  normal(e) {
    this.tick(); e=this.whnf(e);
    if(["sort","var","const"].includes(e[0])) return e;
    return this.make(e[0],...e.slice(1).map(x=>this.normal(x)));
  }
  equal(a,b) {
    this.tick();
    if(this.same(a,b)) return;
    const x=this.normal(a),y=this.normal(b);
    if(this.same(x,y)) return;
    if(x[0]==="sort" && y[0]==="sort") this.reject("sort-mismatch");
    // Eta and proof irrelevance are not implemented. A failed comparison is not evidence of inequality.
    this.unknown("conversion-frontier");
  }
  sortOf(e,ctx) {
    const t=this.whnf(this.infer(e,ctx));
    if(t[0]!=="sort") this.reject("not-a-type");
    return t[1];
  }
  infer(e,ctx) {
    this.tick();
    switch(e[0]) {
      case "sort": this.need("sort"); return this.make("sort",e[1]+1);
      case "var":
        this.need("binders");
        if(e[1]>=ctx.length) this.reject("unbound-variable");
        return this.shift(ctx[ctx.length-1-e[1]],e[1]+1);
      case "const":
        this.need("declarations");
        if(!this.env.has(e[1])) this.reject("undeclared-constant");
        return this.env.get(e[1]).type;
      case "pi": {
        this.need("binders");
        const a=this.sortOf(e[1],ctx), b=this.sortOf(e[2],[...ctx,e[1]]);
        return this.make("sort",b===0 ? 0 : Math.max(a,b));
      }
      case "lam":
        this.need("binders"); this.sortOf(e[1],ctx);
        return this.make("pi",e[1],this.infer(e[2],[...ctx,e[1]]));
      case "app": {
        this.need("application");
        const f=this.whnf(this.infer(e[1],ctx));
        if(f[0]!=="pi") this.reject("not-a-function");
        this.equal(this.infer(e[2],ctx),f[1]);
        return this.substitute(f[2],e[2]);
      }
      case "let":
        this.need("reduction"); this.sortOf(e[1],ctx);
        this.equal(this.infer(e[2],ctx),e[1]);
        return this.infer(this.substitute(e[3],e[2]),ctx);
      default: this.unknown("inference-frontier");
    }
  }
}
const API={Kernel,ACCEPT,REJECT,UNKNOWN,S,V,Pi,Lam,App,Let};

function checkExport(input,capabilities,budget=200000) {
  const start=Date.now();let parsed=0;
  const out=(status,reason)=>({status,reason,parse_records:parsed,elapsed_ms:Date.now()-start});
  if(!capabilities.length) return out(UNKNOWN,"empty-present");
  if(input.length>2000000) return out(UNKNOWN,"input-budget");
  const names=new Map([[0,"[]"]]),levels=new Map([[0,0]]),exprs=new Map(),decls=[];
  const fail=reason=>{throw new Stop(UNKNOWN,reason);};
  const get=(m,n)=>{if(!Number.isSafeInteger(n)||n<0||!m.has(n)) fail("unresolved-reference");return m.get(n);};
  const put=(m,n,v)=>{if(!Number.isSafeInteger(n)||n<0||m.has(n)) fail("duplicate-or-invalid-index");m.set(n,v);};
  let header=false;
  try {
    for(const line of input.split(/\r?\n/)) {
      if(!line.trim()) continue;
      if(++parsed>20000) fail("record-budget");
      const row=JSON.parse(line);
      if(!row || Array.isArray(row)||typeof row!=="object") fail("record-schema");
      const keys=Object.keys(row);
      if(!header) {
        if(keys.length!==1 || keys[0]!=="meta" || row.meta?.format?.version!=="3.1.0") fail("export-version");
        header=true;continue;
      }
      const refs=keys.filter(k=>["in","il","ie"].includes(k));
      const tags=keys.filter(k=>!["in","il","ie"].includes(k));
      if(tags.length!==1 || refs.length>1) fail("record-schema");
      const tag=tags[0],v=row[tag];
      if(refs[0]==="in") {
        if(tag==="str" && v && typeof v.str==="string") put(names,row.in,JSON.stringify([get(names,v.pre),"str",v.str]));
        else if(tag==="num" && v && Number.isSafeInteger(v.i)&&v.i>=0) put(names,row.in,JSON.stringify([get(names,v.pre),"num",v.i]));
        else fail("name-frontier");
      } else if(refs[0]==="il") {
        if(tag==="succ") put(levels,row.il,get(levels,v)+1);
        else if((tag==="max"||tag==="imax")&&Array.isArray(v)&&v.length===2) {
          const a=get(levels,v[0]),b=get(levels,v[1]);
          put(levels,row.il,tag==="imax"&&b===0?0:Math.max(a,b));
        } else fail("universe-frontier");
      } else if(refs[0]==="ie") {
        let e;
        if(tag==="sort") e=S(get(levels,v));
        else if(tag==="bvar" && Number.isSafeInteger(v)&&v>=0) e=V(v);
        else if(tag==="const" && v && Array.isArray(v.us)&&v.us.length===0) e=["const",get(names,v.name)];
        else if((tag==="lam"||tag==="forallE")&&v) e=[tag==="lam"?"lam":"pi",get(exprs,v.type),get(exprs,v.body)];
        else if(tag==="app"&&v) e=App(get(exprs,v.fn),get(exprs,v.arg));
        else if(tag==="letE"&&v&&typeof v.nondep==="boolean") e=Let(get(exprs,v.type),get(exprs,v.value),get(exprs,v.body));
        else if(tag==="mdata"&&v) e=get(exprs,v.expr);
        else fail("expression-frontier:"+tag);
        put(exprs,row.ie,e);
      } else if(tag==="axiom"||tag==="def") {
        if(!v || !Array.isArray(v.levelParams)||v.levelParams.length) fail("declaration-universes");
        if(tag==="axiom" && v.isUnsafe!==false) fail("unsafe-axiom");
        if(tag==="def" && v.safety!=="safe") fail("unsafe-definition");
        const d={kind:tag,name:get(names,v.name),type:get(exprs,v.type)};
        if(tag==="def") d.value=get(exprs,v.value);
        decls.push(d);
      } else fail("declaration-frontier:"+tag);
    }
    if(!header) fail("missing-header");
    const result=new Kernel(capabilities,budget).run(S(0),S(1),decls);
    return {...result,parse_records:parsed,elapsed_ms:Date.now()-start};
  } catch(e) {
    if(e instanceof Stop) return out(e.status,e.message);
    if(e instanceof SyntaxError || e instanceof TypeError || e instanceof RangeError) return out(UNKNOWN,"malformed-or-resource-limited-export");
    throw e;
  }
}

export {Stop,Kernel,ACCEPT,REJECT,UNKNOWN,S,V,Pi,Lam,App,Let,checkExport};
