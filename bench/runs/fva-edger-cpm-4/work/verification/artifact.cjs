// Execute the original Emscripten side module with a small, checked C-ABI host.
const fs = require('fs');
const crypto = require('crypto');
const assert = require('assert/strict');
const bytes = fs.readFileSync('edgeR.so');
assert.equal(bytes.length, 96558);
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb');
const mod = new WebAssembly.Module(bytes);

function cpm(counts, libraries, nrow = 1) {
  const ncol = libraries.length;
  assert.equal(counts.length, nrow * ncol);
  const memory = new WebAssembly.Memory({initial: 16});
  const view = new DataView(memory.buffer);
  let next = 131072;
  const live = new Map();
  const calls = [];
  function calloc(n, size) {
    const length = n * size;
    assert(length > 0 && next + length < memory.buffer.byteLength);
    const p = next;
    next = (next + length + 7) & ~7;
    new Uint8Array(memory.buffer, p, length).fill(0);
    live.set(p, length);
    calls.push(['calloc', n, size]);
    return p;
  }
  function free(p) {
    assert(live.has(p));
    live.delete(p);
    calls.push(['free', p]);
  }
  const imports = {};
  for (const item of WebAssembly.Module.imports(mod)) {
    const env = imports[item.module] ??= {};
    if (item.kind === 'function') {
      env[item.name] = (...args) => {
        throw Error(`unexpected import ${item.module}.${item.name}(${args})`);
      };
    } else if (item.kind === 'memory') env[item.name] = memory;
    else if (item.kind === 'table')
      env[item.name] = new WebAssembly.Table({initial: 16, element: 'anyfunc'});
    else if (item.kind === 'global') {
      const mutable = !['__memory_base', '__table_base'].includes(item.name);
      const value = item.name === '__stack_pointer' ? 1048576 : 0;
      env[item.name] = new WebAssembly.Global({value: 'i32', mutable}, value);
    } else throw Error(`unsupported import kind ${item.kind}`);
  }
  imports.env.R_chk_calloc = calloc;
  imports.env.R_chk_free = free;
  const inst = new WebAssembly.Instance(mod, imports);
  const y = 32768, libs = y + 32, output = y + 64;
  const libdata = output + counts.length * 8;
  // wasm32 cmx: dmat, imat, nrow, ncol, type, isint, pnrow, rowsel.
  [output, 0, nrow, ncol, 0, 0, nrow, 0].forEach((x, i) => view.setInt32(y + 4*i, x, true));
  [libdata, 0, nrow, ncol, 2, 0, nrow, 0].forEach((x, i) => view.setInt32(libs + 4*i, x, true));
  counts.forEach((x, i) => view.setFloat64(output + 8*i, x, true));
  libraries.forEach((x, i) => view.setFloat64(libdata + 8*i, x, true));
  inst.exports.calc_cpm_raw(y, libs, output, 1);
  assert.equal(live.size, 0);
  assert.deepEqual(calls.slice(0, 2), [['calloc', 1, 4], ['calloc', ncol, 8]]);
  assert.equal(calls.length, 4);
  return counts.map((_, i) => view.getFloat64(output + 8*i, true));
}

module.exports = {cpm};
if (require.main === module) {
  if (process.argv[2] === 'cpm') {
    const {counts, libraries, nrow} = JSON.parse(fs.readFileSync(0, 'utf8'));
    // R's scan reads Inf; JSON cannot represent it.
    console.log(cpm(counts, libraries, nrow).map(String).join(' '));
  } else {
    const c = 2**1023, L = c;
    const [actual] = cpm([c], [L]);
    const expected = (c / L) * 1e6;
    assert.equal(actual, Infinity);
    assert.equal(expected, 1000000);
    console.log('R1 counterexample: c=L=2^1023; artifact=+Infinity; required=1000000; no finite error bound.');
    assert.deepEqual(cpm([10], [1e6]), [10]);
    console.log('Control: c=10, L=1000000; artifact=10.');
  }
}
