// Execute the original module. Only allocation imports may run in this fixture.
const fs = require('node:fs');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const bytes = fs.readFileSync('edgeR.so');
assert.equal(bytes.length, 96558);
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb');
const module_ = new WebAssembly.Module(bytes);
const memory = new WebAssembly.Memory({initial:64});
const table = new WebAssembly.Table({initial:1024, element:'anyfunc'});
const view = new DataView(memory.buffer);
let heap = 1048576;
const allocations = new Set();
function calloc(n, size) {
  assert(n >= 0 && size >= 0);
  const ptr = heap;
  heap = (heap + n*size + 7) & ~7;
  assert(heap < 2000000);
  new Uint8Array(memory.buffer, ptr, n*size).fill(0);
  allocations.add(ptr);
  return ptr;
}
const imports = {};
for (const imp of WebAssembly.Module.imports(module_)) {
  const ns = imports[imp.module] ??= {};
  if (imp.kind === 'function') {
    ns[imp.name] = imp.name === 'R_chk_calloc' ? calloc :
      imp.name === 'R_chk_free' ? p => assert(allocations.delete(p)) :
      () => { throw Error('Unexpected import: '+imp.module+'.'+imp.name); };
  } else if (imp.kind === 'memory') ns[imp.name] = memory;
  else if (imp.kind === 'table') ns[imp.name] = table;
  else if (imp.name === '__memory_base') ns[imp.name] = 1024;
  else if (imp.name === '__table_base') ns[imp.name] = 1;
  else ns[imp.name] = new WebAssembly.Global({value:'i32', mutable:true},
    imp.name === '__stack_pointer' ? 3000000 : 131072);
}
const {exports: exp} = new WebAssembly.Instance(module_, imports);
function cmx(ptr, data, nr, nc, type) {
  // wasm32 cmx layout from src/edgeR.h; full double matrix or repeated row.
  const fields = [data,0,nr,nc,type,0,nr,0];
  fields.forEach((x,i) => view.setInt32(ptr+4*i,x,true));
}
function run(counts, libs, nr, nc) {
  const y=262144, lib=262176, cp=262208, lp=270400;
  counts.forEach((x,i)=>view.setFloat64(cp+8*i,x,true));
  libs.forEach((x,i)=>view.setFloat64(lp+8*i,x,true));
  cmx(y,cp,nr,nc,0); cmx(lib,lp,nr,nc,2);
  exp.calc_cpm_raw(y,lib,cp,1);
  assert.equal(allocations.size,0);
  return counts.map((_,i)=>view.getFloat64(cp+8*i,true));
}
const c = 2**1020;
const overflow = run([c],[c],1,1)[0];
assert.equal(overflow, Infinity);
assert.equal(c/c*1e6, 1000000);
console.log('R1: c=L=2^1020; actual=Infinity; exact CPM=1000000');
const result = run([10,8,10,8],[18,18],2,2);
assert.deepEqual(result,[10*1e6/18,8*1e6/18,10*1e6/18,8*1e6/18]);
assert.equal(result[0], 555555.5555555555);
assert.equal(10/18*1e6, 555555.5555555556);
fs.writeFileSync('verification/cpm.csv', 'a,b\n'+result[0]+','+result[2]+'\n'+result[1]+','+result[3]+'\n');
console.log('R2: c=10, L=18; actual CPM='+result[0]+' < cutoff='+(10/18*1e6));
console.log('Artifact checks passed');
