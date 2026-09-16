import assert from "node:assert/strict";
import {appendName,atomName,displayName,leanName,nameComponents} from "./name-codec.mjs";

const structured=leanName("A","b.c","[q]","\\slash\"");
assert.deepEqual(nameComponents(structured),[
  ["str","A"],["str","b.c"],["str","[q]"],["str","\\slash\""]
]);
assert.equal(displayName(structured),'A.b.c.[q].\\slash"');

assert.notEqual(appendName(leanName("A"),"str","7"),appendName(leanName("A"),"num",7),
  "string and numeric components must not collide");
assert.notEqual(atomName(structured),structured,
  "an arbitrary atom that resembles an encoded structured name must retain atomic identity");
assert.notEqual(appendName("A","str","b"),leanName("A","b"),
  "a child of the arbitrary atom A is distinct from a root-structured A.b");

let deep=leanName();
for(let i=0;i<500;i++) deep=appendName(deep,"str",`x${i}`);
assert.equal(nameComponents(deep).length,500);
assert.ok(deep.length<10_000,`deep flat name grew unexpectedly: ${deep.length}`);

console.log("NAME_CODEC_PASS");
