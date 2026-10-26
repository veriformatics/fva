// Run the ORIGINAL binary. No C recompilation or arithmetic replacement.
import fs from 'node:fs';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
const bytes = fs.readFileSync('edgeR.so');
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb');
const mod = new WebAssembly.Module(bytes);
const memory = new WebAssembly.Memory({initial:32});
const table = new WebAssembly.Table({initial:32, element:'anyfunc'});
const view = new DataView(memory.buffer);
let heap = 131072;
const imports = {};
for (const i of WebAssembly.Module.imports(mod)) {
  const ns = imports[i.module] ??= {};
  if (i.kind === 'memory') ns[i.name] = memory;
  else if (i.kind === 'table') ns[i.name] = table;
  else if (i.kind === 'global') ns[i.name] = new WebAssembly.Global(
    {value:'i32', mutable: !['__memory_base','__table_base'].includes(i.name)},
    i.name === '__stack_pointer' ? 1048576 : i.name === '__memory_base' ? 1024 : 0);
  else ns[i.name] = () => { throw Error(`Unexpected host call ${i.module}.${i.name}`); };
}
imports.env.R_chk_calloc = (n, size) => {
  assert(n >= 0 && size >= 0);
  const p = heap;
  heap += Math.ceil(n * size / 8) * 8;
  assert(heap < 900000);
  new Uint8Array(memory.buffer, p, heap-p).fill(0);
  return p;
};
imports.env.R_chk_free = () => {}; // bump allocations live until this process exits
const api = new WebAssembly.Instance(mod, imports).exports;
function cpm(nrow, ncol, counts, libs) {
  assert.equal(counts.length, nrow*ncol);
  assert.equal(libs.length, nrow*ncol);
  assert(nrow*ncol <= 512);
  counts.forEach((x,i) => view.setFloat64(40000+8*i,x,true));
  libs.forEach((x,i) => view.setFloat64(50000+8*i,x,true));
  // Call the shipped struct constructor: sret,dmat,imat,nrow,ncol,type,isint.
  api.make_cmx(32768,40000,0,nrow,ncol,0,0);
  api.make_cmx(32800,50000,0,nrow,ncol,0,0);
  api.calc_cpm_raw(32768,32800,40000,1);
  return counts.map((_,i) => view.getFloat64(40000+8*i,true));
}
const bits = x => { const b = Buffer.alloc(8); b.writeDoubleLE(x); return b.readBigUInt64LE().toString(16); };
if (process.argv[2] === 'matrix') {
  const x = JSON.parse(fs.readFileSync(0,'utf8'));
  console.log(JSON.stringify(cpm(x.nrow,x.ncol,x.counts,x.libs)));
} else {
  const overflow = cpm(1,1,[2**1020],[2**1020])[0];
  assert.equal(overflow,Infinity);
  const outputs = cpm(2,2,[10,8,10,8],[18,18,18,18]);
  assert.deepEqual(outputs.map(bits),['4120f4471c71c71c','411b2071c71c71c7',
    '4120f4471c71c71c','411b2071c71c71c7']);
  assert.equal(bits(10/18*1e6),'4120f4471c71c71d');
  if (process.argv[2] === 'negative') assert.equal(outputs[0],0);
  console.log('V8: R1 output = +Infinity; exact target = 1000000');
  console.log('V8: R2 CPM bits = '+bits(outputs[0])+'; cutoff bits = '+bits(10/18*1e6));
}
