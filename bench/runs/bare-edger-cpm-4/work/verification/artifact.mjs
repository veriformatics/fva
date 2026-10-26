// Execute the original, hash-pinned side module. No function body is replaced.
import fs from 'node:fs';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';

const bytes = fs.readFileSync('edgeR.so');
assert.equal(bytes.length, 96558);
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb');
const module = new WebAssembly.Module(bytes);
const memory = new WebAssembly.Memory({initial: 16});
const view = new DataView(memory.buffer);
let next = 0x30000;
const live = new Set();
function calloc(n, size) {
  assert(Number.isInteger(n) && n > 0 && Number.isInteger(size) && size > 0);
  const p = next;
  next += Math.ceil(n * size / 8) * 8;
  assert(next < memory.buffer.byteLength);
  new Uint8Array(memory.buffer, p, next - p).fill(0);
  live.add(p);
  return p;
}
function free(p) { assert(live.delete(p)); }
const imports = {};
for (const {module: ns, name, kind} of WebAssembly.Module.imports(module)) {
  imports[ns] ??= {};
  if (kind === 'function') {
    imports[ns][name] = name === 'R_chk_calloc' ? calloc
      : name === 'R_chk_free' ? free
      : () => { throw new Error(`Unexpected import called: ${ns}.${name}`); };
  } else if (kind === 'memory') imports[ns][name] = memory;
  else if (kind === 'table') imports[ns][name] = new WebAssembly.Table({initial: 16, element: 'anyfunc'});
  else if (kind === 'global') {
    const mutable = !['__memory_base', '__table_base'].includes(name);
    const value = name === '__stack_pointer' ? 0x20000 : name === '__table_base' ? 1 : 0;
    imports[ns][name] = new WebAssembly.Global({value: 'i32', mutable}, value);
  } else throw new Error(`Unexpected import kind ${kind}`);
}
const {exports: wasm} = new WebAssembly.Instance(module, imports);

function cpm(nrow, ncol, counts, libs) {
  assert(Number.isInteger(nrow) && nrow > 0 && Number.isInteger(ncol) && ncol > 0);
  assert.equal(counts.length, nrow * ncol);
  assert.equal(libs.length, ncol);
  assert(counts.every(x => Number.isFinite(x) && x >= 0));
  assert(libs.every(x => Number.isFinite(x) && x > 0));
  const baseline = live.size;
  const y = calloc(1, 32), l = calloc(1, 32);
  const data = calloc(counts.length, 8), ld = calloc(libs.length, 8);
  counts.forEach((v, i) => view.setFloat64(data + 8 * i, v, true));
  libs.forEach((v, i) => view.setFloat64(ld + 8 * i, v, true));
  // make_cmx writes the actual artifact's cmx layout; type 2 repeats a row.
  wasm.make_cmx(y, data, 0, nrow, ncol, 0, 0);
  wasm.make_cmx(l, ld, 0, nrow, ncol, 2, 0);
  wasm.calc_cpm_raw(y, l, data, 1);
  const result = counts.map((_, i) => view.getFloat64(data + 8 * i, true));
  [y, l, data, ld].forEach(free);
  assert.equal(live.size, baseline);
  return result;
}
function bits(x) {
  const b = new DataView(new ArrayBuffer(8));
  b.setFloat64(0, x, true);
  return b.getBigUint64(0, true).toString(16).padStart(16, '0');
}

if (process.argv[2] === 'cpm') {
  const [nr, nc, ...rest] = process.argv.slice(3).map(Number);
  const result = cpm(nr, nc, rest.slice(0, nr * nc), rest.slice(nr * nc));
  console.log(result.map(String).join('\n'));
} else {
  assert.equal(process.argv.length, 2);
  const c = 2 ** 1023;
  const overflow = cpm(1, 1, [c], [c])[0];
  assert.equal(overflow, Infinity);
  assert.equal(c / c * 1e6, 1000000);
  console.log(`R1: c=L=2^1023, output=${overflow}, bits=${bits(overflow)}, target=1000000`);
  const boundary = cpm(1, 2, [10, 10], [18, 18]);
  boundary.forEach(x => assert.equal(bits(x), '4120f4471c71c71c'));
  assert.equal(bits(10 / 18 * 1e6), '4120f4471c71c71d');
  console.log(`R2 boundary: CPM bits=${boundary.map(bits)}, cutoff bits=${bits(10 / 18 * 1e6)}`);
  assert.deepEqual(cpm(1, 1, [10], [1000000]), [10]);
  console.log('PASS: all artifact assertions');
}
