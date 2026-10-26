// Executes the original edgeR.so; no numerical algorithm is reimplemented here.
const fs = require('fs');
const crypto = require('crypto');
const assert = require('assert/strict');
const bytes = fs.readFileSync('edgeR.so');
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb');
const mod = new WebAssembly.Module(bytes);
const memory = new WebAssembly.Memory({initial: 16});
const table = new WebAssembly.Table({initial: 100, element: 'anyfunc'});
const view = new DataView(memory.buffer);
let heap = 65536;
const calls = [];
function alloc(n, size) {
  const p = heap;
  heap = (heap + n * size + 7) & ~7;
  assert(heap < 524288);
  new Uint8Array(memory.buffer, p, heap - p).fill(0);
  return p;
}
const imports = {};
for (const imp of WebAssembly.Module.imports(mod)) {
  const ns = imports[imp.module] ??= {};
  if (imp.kind === 'memory') ns[imp.name] = memory;
  else if (imp.kind === 'table') ns[imp.name] = table;
  else if (imp.kind === 'global') {
    const mutable = !['__memory_base', '__table_base'].includes(imp.name);
    ns[imp.name] = new WebAssembly.Global({value: 'i32', mutable},
      imp.name === '__stack_pointer' ? 900000 : 0);
  } else if (imp.name === 'R_chk_calloc') ns[imp.name] = (n, s) => {
    calls.push(imp.name); return alloc(n, s);
  };
  else if (imp.name === 'R_chk_free') ns[imp.name] = p => {
    assert(p >= 65536 && p < heap); calls.push(imp.name);
  };
  else ns[imp.name] = () => {throw new Error('Unexpected host call: ' + imp.name);};
}
const instance = new WebAssembly.Instance(mod, imports);
function raw(counts, libs, nr, nc) {
  assert.equal(counts.length, nr * nc);
  assert.equal(libs.length, nc);
  const out = alloc(counts.length, 8);
  counts.forEach((x, i) => view.setFloat64(out + 8 * i, x, true));
  const lp = alloc(nc, 8);
  libs.forEach((x, i) => view.setFloat64(lp + 8 * i, x, true));
  function cmx(data, type) {
    const p = alloc(8, 4);
    // src/edgeR.h: dmat, imat, nrow, ncol, type, isint, pnrow, rowsel.
    [data, 0, nr, nc, type, 0, nr, 0].forEach((x, i) => view.setInt32(p + 4*i, x, true));
    return p;
  }
  const y = cmx(out, 0), lib = cmx(lp, 2);
  calls.length = 0;
  instance.exports.calc_cpm_raw(y, lib, out, 1);
  assert.deepEqual(calls, ['R_chk_calloc', 'R_chk_calloc', 'R_chk_free', 'R_chk_free']);
  return counts.map((_, i) => view.getFloat64(out + 8 * i, true));
}
function bits(x) {
  const b = Buffer.alloc(8); b.writeDoubleLE(x); return b.readBigUInt64LE().toString(16);
}
if (process.argv[2] === '--matrix') {
  const input = JSON.parse(fs.readFileSync(0, 'utf8'));
  raw(input.counts, input.libs, input.nr, input.nc).forEach(x => console.log(String(x)));
} else {
  const c = 2 ** 1023;
  const overflow = raw([c], [c], 1, 1)[0];
  assert.equal(overflow, Infinity);
  assert.equal((c / c) * 1e6, 1e6);
  console.log('R1: c = L = 2^1023; actual = +Infinity; required = 1000000');
  const boundary = raw([10, 10], [18, 18], 1, 2);
  assert.deepEqual(boundary.map(bits), ['4120f4471c71c71c', '4120f4471c71c71c']);
  assert.equal(bits(10 / 18 * 1e6), '4120f4471c71c71d');
  assert.equal(raw([10], [1e6], 1, 1)[0], 10);
  console.log('R2: CPM bits = 0x4120f4471c71c71c; cutoff bits = 0x4120f4471c71c71d');
  console.log('WASM COUNTEREXAMPLES PASS');
}
