// Persistent closure environment for the Arena kernel evaluator.
//
// This module deliberately starts below Lean semantics: it implements only the
// exact lambda/let substitution machinery.  Declaration, recursor, projection
// and quotient rules are added only after differential tests earn them.

export const emptyClosureEnv=Object.freeze({kind:"empty",length:0});

export function makeClosure(expr,env=emptyClosureEnv){
  if(!Array.isArray(expr)) throw new TypeError("closure expression must be an expression array");
  if(!env||!Number.isSafeInteger(env.length)||env.length<0) throw new TypeError("invalid closure environment");
  return {expr,env};
}

export function extendClosureEnv(env,value){
  if(!env||!Number.isSafeInteger(env.length)||env.length<0) throw new TypeError("invalid closure environment");
  if(!value||!Array.isArray(value.expr)||!value.env) throw new TypeError("closure environment values must be closures");
  return {kind:"bind",value,next:env,length:env.length+1};
}

export function lookupClosureVar(env,index){
  if(!Number.isSafeInteger(index)||index<0) throw new RangeError("invalid de Bruijn index");
  let cur=env,i=index;
  while(cur&&cur.kind==="bind"){
    if(i===0) return cur.value;
    i--; cur=cur.next;
  }
  return null;
}

function shiftRaw(expr,amount,cut=0){
  if(amount===0) return expr;
  switch(expr[0]){
    case "sort": case "const": case "nat": case "strlit": return expr;
    case "var": return expr[1]<cut?expr:["var",expr[1]+amount];
    case "pi": case "lam": return [expr[0],shiftRaw(expr[1],amount,cut),shiftRaw(expr[2],amount,cut+1)];
    case "app": return ["app",shiftRaw(expr[1],amount,cut),shiftRaw(expr[2],amount,cut)];
    case "proj": return ["proj",expr[1],expr[2],shiftRaw(expr[3],amount,cut)];
    case "let": return ["let",shiftRaw(expr[1],amount,cut),shiftRaw(expr[2],amount,cut),shiftRaw(expr[3],amount,cut+1)];
    default: throw new Error(`unsupported closure reification syntax: ${String(expr[0])}`);
  }
}

function reifyExpr(expr,env,boundDepth){
  switch(expr[0]){
    case "sort": case "const": case "nat": case "strlit": return expr;
    case "var": {
      const index=expr[1];
      if(index<boundDepth) return expr;
      const outer=index-boundDepth;
      const value=lookupClosureVar(env,outer);
      if(value!==null) return shiftRaw(reifyExpr(value.expr,value.env,0),boundDepth,0);
      return env.length===0?expr:["var",index-env.length];
    }
    case "pi": case "lam":
      return [expr[0],reifyExpr(expr[1],env,boundDepth),reifyExpr(expr[2],env,boundDepth+1)];
    case "app":
      return ["app",reifyExpr(expr[1],env,boundDepth),reifyExpr(expr[2],env,boundDepth)];
    case "proj":
      return ["proj",expr[1],expr[2],reifyExpr(expr[3],env,boundDepth)];
    case "let":
      return ["let",reifyExpr(expr[1],env,boundDepth),reifyExpr(expr[2],env,boundDepth),reifyExpr(expr[3],env,boundDepth+1)];
    default: throw new Error(`unsupported closure reification syntax: ${String(expr[0])}`);
  }
}

export function reifyClosure(closure){
  if(!closure||!Array.isArray(closure.expr)||!closure.env) throw new TypeError("expected closure");
  return reifyExpr(closure.expr,closure.env,0);
}

function rebuildNeutral(head,args){
  let raw=reifyClosure(head);
  while(args.length) raw=["app",raw,reifyClosure(args.pop())];
  return makeClosure(raw,emptyClosureEnv);
}

// Iterative beta/let WHNF.  No recursive call is made while following the
// reduction spine, so deeply nested beta chains do not consume the host stack.
export function nativeWhnf(term){
  let cur=term&&Array.isArray(term.expr)?term:makeClosure(term,emptyClosureEnv);
  const args=[];
  while(true){
    const e=cur.expr;
    switch(e[0]){
      case "app":
        args.push(makeClosure(e[2],cur.env));
        cur=makeClosure(e[1],cur.env);
        continue;
      case "let":
        cur=makeClosure(e[3],extendClosureEnv(cur.env,makeClosure(e[2],cur.env)));
        continue;
      case "var": {
        const value=lookupClosureVar(cur.env,e[1]);
        if(value!==null){cur=value;continue;}
        if(cur.env.length!==0) cur=makeClosure(["var",e[1]-cur.env.length],emptyClosureEnv);
        if(args.length) return rebuildNeutral(cur,args);
        return cur;
      }
      case "lam":
        if(args.length){
          const arg=args.pop();
          cur=makeClosure(e[2],extendClosureEnv(cur.env,arg));
          continue;
        }
        return cur;
      default:
        if(args.length) return rebuildNeutral(cur,args);
        return cur;
    }
  }
}
