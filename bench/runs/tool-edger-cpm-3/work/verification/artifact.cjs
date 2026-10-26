'use strict';
// Run the original, unmodified side module with a small Emscripten host.
const fs = require('node:fs');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const bytes = fs.readFileSync('edgeR.so');
assert.equal(bytes.length, 96558);
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb');
const module_ = new WebAssembly.Module(bytes);
const memory = new WebAssembly.Memory({initial: 64});
const view = new DataView(memory.buffer);
const table = new WebAssembly.Table({initial: 128, element: 'anyfunc'});
let heap = 1200000;
const allocations = new Map();
const calls = [];
function calloc(n, size) {
  assert(n >= 0 && size >= 0);
  const count = n * size;
  const ptr = heap;
  heap = (heap + count + 15) & ~15;
  assert(heap < memory.buffer.byteLength);
  new Uint8Array(memory.buffer, ptr, count).fill(0);
  allocations.set(ptr, count);
  calls.push(['calloc', n, size]);
  return ptr;
}
function free(ptr) {
  assert(allocations.has(ptr));
  allocations.delete(ptr);
  calls.push(['free']);
}
const imports = {};
let got = 60000;
for (const {module, name, kind} of WebAssembly.Module.imports(module_)) {
  imports[module] ??= {};
  if (kind === 'memory') imports[module][name] = memory;
  else if (kind === 'table') imports[module][name] = table;
  else if (kind === 'global') {
    const value = name === '__stack_pointer' ? 1000000 :
      name === '__memory_base' ? 1024 : name === '__table_base' ? 0 : (got += 8);
    imports[module][name] = new WebAssembly.Global(
      {value: 'i32', mutable: name === '__stack_pointer' || module.startsWith('GOT.')}, value);
  } else if (name === 'R_chk_calloc') imports[module][name] = calloc;
  else if (name === 'R_chk_free') imports[module][name] = free;
  else imports[module][name] = () => { throw new Error(`Unexpected import ${module}.${name}`); };
}
const instance = new WebAssembly.Instance(module_, imports);
// No constructors are needed by this kernel; the module start runs normally.
// cmx is the wasm32 layout from edgeR.h (32 bytes), type 2 = repeated row.
function cmx(ptr, data, nrow, ncol, type) {
  [data, 0, nrow, ncol, type, 0, nrow, 0].forEach((x, i) => view.setInt32(ptr + 4*i, x, true));
}
function bits(value) {
  const buf = Buffer.alloc(8);
  buf.writeDoubleLE(value);
  return buf.readBigUInt64LE().toString(16).padStart(16, '0');
}
function run(counts, libs, nrow, ncol) {
  assert.equal(counts.length, nrow*ncol);
  assert.equal(libs.length, ncol);
  assert(nrow > 0 && ncol > 0 && nrow*ncol <= 10000);
  assert(counts.every(c => Number.isFinite(c) && c >= 0));
  assert(libs.every(l => Number.isFinite(l) && l > 0));
  const y = 100000, ls = 100032, cpm = 110000, ldata = 210000;
  cmx(y, cpm, nrow, ncol, 0);
  cmx(ls, ldata, nrow, ncol, 2);
  counts.forEach((c,i) => view.setFloat64(cpm + 8*i, c, true));
  libs.forEach((l,i) => view.setFloat64(ldata + 8*i, l, true));
  const from = calls.length;
  instance.exports.calc_cpm_raw(y, ls, cpm, 1);
  assert.equal(allocations.size, 0);
  assert.deepEqual(calls.slice(from), [['calloc',1,4],['calloc',ncol,8],['free'],['free']]);
  const values = counts.map((_,i) => view.getFloat64(cpm + 8*i, true));
  return values;
}
if (process.argv[2] === '--matrix') {
  const {counts, libs, nrow, ncol} = JSON.parse(fs.readFileSync(0, 'utf8'));
  const values = run(counts, libs, nrow, ncol);
  assert(values.every(Number.isFinite));
  process.stdout.write(JSON.stringify(values));
} else {
  assert.equal(bits(1e308), '7fe1ccf385ebc8a0');
  const overflow = run([1e308], [1e308], 1, 1)[0];
  assert.equal(overflow, Infinity);
  const correct = (1e308 / 1e308) * 1e6;
  assert.equal(correct, 1000000);
  const boundary = run([10,10], [1000009,1000009], 1, 2);
  assert.deepEqual(boundary.map(bits), ['4023fff43420d831','4023fff43420d831']);
  const cutoff = (10 / 1000009) * 1e6;
  assert.equal(bits(cutoff), '4023fff43420d832');
  assert(boundary.every(c => c < cutoff));
  console.log(`R1: c=L=1e308, actual=${overflow}, exact CPM=${correct}`);
  console.log(`R2: actual CPM bits=${boundary.map(bits)}, cutoff bits=${bits(cutoff)}`);
  console.log('ARTIFACT COUNTEREXAMPLES PASS');
}
