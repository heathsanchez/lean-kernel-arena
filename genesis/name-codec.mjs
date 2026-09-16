const MARKER="$lean-name-v1";
const ROOT=JSON.stringify([MARKER]);

function parseName(name) {
  if(typeof name!=="string") return null;
  let value;
  try { value=JSON.parse(name); } catch { return null; }
  if(!Array.isArray(value)||value[0]!==MARKER) return null;
  for(let i=1;i<value.length;i++) {
    const c=value[i];
    if(!Array.isArray(c)||c.length!==2||
       !((c[0]==="str"&&typeof c[1]==="string")||
         (c[0]==="num"&&Number.isSafeInteger(c[1])&&c[1]>=0)||
         (i===1&&c[0]==="atom"&&typeof c[1]==="string"))) return null;
  }
  return value;
}

function atomName(value) {
  if(typeof value!=="string") throw new TypeError("name atom must be a string");
  return JSON.stringify([MARKER,["atom",value]]);
}

function appendName(prefix,tag,payload) {
  if(!((tag==="str"&&typeof payload==="string")||
       (tag==="num"&&Number.isSafeInteger(payload)&&payload>=0)))
    throw new TypeError("invalid name component");
  const parts=parseName(prefix)??[MARKER,["atom",prefix]];
  return JSON.stringify([...parts,[tag,payload]]);
}

function leanName(...parts) {
  let name=ROOT;
  for(const part of parts) name=appendName(name,"str",part);
  return name;
}

function nameComponents(name) {
  const parts=parseName(name);
  if(!parts) return [["atom",name]];
  return parts.slice(1).map(([tag,payload])=>[tag,payload]);
}

function displayName(name) {
  return nameComponents(name).map(([,payload])=>String(payload)).join(".");
}

export {appendName,atomName,displayName,leanName,nameComponents,ROOT};
