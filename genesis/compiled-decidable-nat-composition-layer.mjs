import {Kernel} from "./kernel-base.mjs";

// Exact composition layer: reuse already-retained closed Nat reductions inside
// Decidable.decide for Nat <.  This adds no new arithmetic semantics: it only
// fires when both proposition operands and both Nat.decLt operands normalize
// through the previously retained WHNF stack to the same Nat literals.
const p=Kernel.prototype, whnf0=p.whnf;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
const NAT=N("Nat"), DECIDE=N("Decidable","decide"), NAT_DECLT=N("Nat","decLt"),
  LT_LT=N("LT","lt"), INST_LT_NAT=N("instLTNat"), BTRUE=N("Bool","true"), BFALSE=N("Bool","false");

function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return{h,args};}
function isConst(e,name){return Array.isArray(e)&&e[0]==="const"&&e[1]===name;}
function literalAfterRetained(k,e){
  const r=whnf0.call(k,e);
  if(!Array.isArray(r)||r[0]!=="nat")return null;
  try{return BigInt(r[1]);}catch{return null;}
}
function natLtShape(e){
  const {h,args}=spine(e);
  if(h?.[0]!=="const"||h[1]!==LT_LT||args.length!==4||!isConst(args[0],NAT)||!isConst(args[1],INST_LT_NAT))return null;
  return [args[2],args[3]];
}
function decLtShape(e){
  const {h,args}=spine(e);
  if(h?.[0]!=="const"||h[1]!==NAT_DECLT||args.length!==2)return null;
  return [args[0],args[1]];
}

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=spine(e);
    if(h?.[0]==="const"&&h[1]===DECIDE&&args.length===2){
      const ps=natLtShape(args[0]),ds=decLtShape(args[1]);
      if(ps&&ds){
        const pa=literalAfterRetained(this,ps[0]),pb=literalAfterRetained(this,ps[1]);
        const da=literalAfterRetained(this,ds[0]),db=literalAfterRetained(this,ds[1]);
        if(pa!==null&&pb!==null&&da!==null&&db!==null&&pa===da&&pb===db){
          this.need("reduction");this.need("declarations");this.need("nat-literals");
          this.__decisionCompositionHits=(this.__decisionCompositionHits??0)+1;
          return ["const",pa<pb?BTRUE:BFALSE];
        }
      }
    }
  }
  return whnf0.call(this,e);
};
