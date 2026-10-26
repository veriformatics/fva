// Execute the original Wasm, supplying only the host services this path uses.
const fs = require('node:fs');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const bytes = fs.readFileSync('edgeR.so');
assert.equal(bytes.length, 96558);
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb');
const mod = new WebAssembly.Module(bytes);
const memory = new WebAssembly.Memory({initial: 32});
const view = new DataView(memory.buffer);
let heap = 65536;
const live = new Set();
function alloc(n, size = 1) {
  assert(Number.isInteger(n) && n > 0 && Number.isInteger(size) && size > 0);
  const p = heap;
  heap = (heap + n * size + 15) & ~15;
  assert(heap < 1048576, 'heap must not overlap stack');
  new Uint8Array(memory.buffer, p, n * size).fill(0);
  live.add(p);
  return p;
}
const calls = [];
const imports = {};
for (const imp of WebAssembly.Module.imports(mod)) {
  const ns = imports[imp.module] ||= {};
  if (imp.kind === 'function') {
    ns[imp.name] = (...args) => {
      calls.push(imp.name);
      if (imp.module === 'env' && imp.name === 'R_chk_calloc') return alloc(...args);
      if (imp.module === 'env' && imp.name === 'R_chk_free') {
        assert(live.delete(args[0]), 'invalid free');
        return;
      }
      throw Error(`Unexpected host call: ${imp.module}.${imp.name}`);
    };
  } else if (imp.kind === 'global') {
    ns[imp.name] = new WebAssembly.Global({value: 'i32',
      mutable: !['__memory_base', '__table_base'].includes(imp.name)},
      imp.name === '__stack_pointer' ? 1572864 : 0);
  } else if (imp.kind === 'memory') ns[imp.name] = memory;
  else if (imp.kind === 'table') ns[imp.name] =
    new WebAssembly.Table({element: 'anyfunc', initial: 9});
  else throw Error(`Unexpected import kind ${imp.kind}`);
}
const instance = new WebAssembly.Instance(mod, imports);
function matrix(data, nr, nc) {
  assert.equal(data.length, nr * nc);
  const p = alloc(32), d = alloc(data.length, 8);
  data.forEach((x, i) => view.setFloat64(d + 8 * i, x, true));
  // cmx: dmat, imat, nrow, ncol, type, isint, pnrow, rowsel.
  [d, 0, nr, nc, 0, 0, nr, 0].forEach((x, i) => view.setInt32(p + 4*i, x, true));
  return [p, d];
}
function run(counts, libs, nr, nc) {
  assert(nr > 0 && nc > 0);
  assert(counts.every(x => Number.isFinite(x) && x >= 0));
  assert.equal(libs.length, nc);
  assert(libs.every(x => Number.isFinite(x) && x > 0));
  const [y] = matrix(counts, nr, nc);
  const [l] = matrix(libs.flatMap(x => Array(nr).fill(x)), nr, nc);
  const [, out] = matrix(counts, nr, nc);
  const before = new Set(live);
  instance.exports.calc_cpm_raw(y, l, out, 1);
  assert.deepEqual(live, before, 'scratch allocations must be freed');
  return counts.map((_, i) => view.getFloat64(out + 8*i, true));
}
function bits(x) {
  const b = Buffer.alloc(8); b.writeDoubleLE(x);
  return '0x' + b.readBigUInt64LE().toString(16).padStart(16, '0');
}
if (process.argv[2] === '--matrix') {
  const b = fs.readFileSync(process.argv[3]);
  const nr = b.readInt32LE(0), nc = b.readInt32LE(4);
  assert.equal(b.length, 8 + 8 * (nr * nc + nc));
  const values = Array.from({length: nr*nc+nc}, (_, i) => b.readDoubleLE(8+8*i));
  console.log(run(values.slice(0,nr*nc), values.slice(nr*nc), nr, nc).join('\n'));
} else {
  assert.deepEqual(run([10, 20, 0, 40], [1e6, 2e6], 2, 2), [10, 20, 0, 20]);
  const c = 2 ** 1020;
  const [actual] = run([c], [c], 1, 1);
  const expected = (c / c) * 1e6;
  assert.equal(bits(c), '0x7fb0000000000000');
  assert.equal(actual, Infinity);
  assert.equal(expected, 1000000);
  assert.equal(bits(expected), '0x412e848000000000');
  console.log(`R1 FAIL witness: c=L=2^1020; actual=${actual} (${bits(actual)}); exact target=${expected} (${bits(expected)})`);
  console.log('PASS: original artifact hash, execution, and R1 counterexample assertions');
}
