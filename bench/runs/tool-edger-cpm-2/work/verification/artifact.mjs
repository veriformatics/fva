// Execute edgeR.so itself. No arithmetic from compute_cpm.c is substituted.
import fs from 'node:fs';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';

const root = new URL('../', import.meta.url);
const bytes = fs.readFileSync(new URL('edgeR.so', root));
assert.equal(bytes.length, 96558);
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  'e39434314a9eb0399edf943c6a0475d34ff9d0d7ec0bb4a1b8ba726b4a6a88fb');
const module = new WebAssembly.Module(bytes);
// Link the certificate's decimal constants to the intended binary values.
const certificate = fs.readFileSync(new URL('verification/wp.c', root), 'utf8');
function modelInteger(name) {
  const match = certificate.match(new RegExp(`logic integer ${name} = ([0-9]+);`));
  assert(match, `Missing model constant ${name}`);
  return BigInt(match[1]);
}
assert.equal(modelInteger('overflow_count'), 2n ** 1023n);
assert.equal(modelInteger('overflow_midpoint'), 2n ** 1024n - 2n ** 970n);
assert.equal(modelInteger('raw_sig') - 2n**52n + (1042n << 52n),
  0x4120f4471c71c71cn);
assert.equal(modelInteger('cutoff_sig') - 2n**52n + (1042n << 52n),
  0x4120f4471c71c71dn);
assert.equal(modelInteger('div_sig') - 2n**52n + (1022n << 52n),
  0x3fe1c71c71c71c72n);

export function artifactCPM(nrow, ncol, counts, libraries) {
  assert(Number.isInteger(nrow) && nrow > 0 && nrow < 100);
  assert(Number.isInteger(ncol) && ncol > 0 && ncol < 100);
  assert.equal(counts.length, nrow * ncol);
  assert.equal(libraries.length, ncol);
  const memory = new WebAssembly.Memory({initial: 32});
  const view = new DataView(memory.buffer);
  const table = new WebAssembly.Table({initial: 32, element: 'anyfunc'});
  let next = 131072;
  const allocations = new Map();
  const calls = [];
  function calloc(n, size) {
    assert(n >= 0 && size >= 0);
    const length = n * size;
    const ptr = next;
    next += Math.max(8, Math.ceil(length / 8) * 8);
    assert(next < memory.buffer.byteLength);
    new Uint8Array(memory.buffer, ptr, length).fill(0);
    allocations.set(ptr, length);
    return ptr;
  }
  const imports = {};
  for (const imp of WebAssembly.Module.imports(module)) {
    const ns = imports[imp.module] ??= {};
    if (imp.kind === 'function') {
      ns[imp.name] = (...args) => {
        calls.push(imp.name);
        if (imp.module === 'env' && imp.name === 'R_chk_calloc')
          return calloc(...args);
        if (imp.module === 'env' && imp.name === 'R_chk_free') {
          assert(allocations.delete(args[0]));
          return;
        }
        throw new Error(`Unexpected import called: ${imp.module}.${imp.name}`);
      };
    } else if (imp.kind === 'memory') {
      ns[imp.name] = memory;
    } else if (imp.kind === 'table') {
      ns[imp.name] = table;
    } else if (imp.kind === 'global') {
      const immutable = imp.name === '__memory_base' || imp.name === '__table_base';
      ns[imp.name] = new WebAssembly.Global({value: 'i32', mutable: !immutable},
        imp.name === '__stack_pointer' ? 65536 : 0);
    } else {
      throw new Error(`Unsupported import kind ${imp.kind}`);
    }
  }
  const instance = new WebAssembly.Instance(module, imports);
  function doubles(values) {
    const ptr = calloc(values.length, 8);
    values.forEach((x, i) => view.setFloat64(ptr + 8*i, x, true));
    return ptr;
  }
  function cmx(data, type) {
    const ptr = calloc(1, 32);
    // wasm32 cmx: dmat, imat, nrow, ncol, type, isint, pnrow, rowsel.
    [data, 0, nrow, ncol, type, 0, nrow, 0].forEach(
      (x, i) => view.setInt32(ptr + 4*i, x, true));
    return ptr;
  }
  const cpm = doubles(counts);
  const lib = doubles(libraries);
  const y = cmx(cpm, 0);
  const libs = cmx(lib, 2); // Library-size row repeated over genes.
  const callerBlocks = new Map(allocations);
  instance.exports.calc_cpm_raw(y, libs, cpm, 1);
  assert.deepEqual(allocations, callerBlocks, 'scratch was not freed correctly');
  assert.deepEqual(calls, ['R_chk_calloc', 'R_chk_calloc', 'R_chk_free', 'R_chk_free']);
  return counts.map((_, i) => view.getFloat64(cpm + 8*i, true));
}

export function bits(x) {
  const buf = new ArrayBuffer(8);
  const v = new DataView(buf);
  v.setFloat64(0, x, true);
  return '0x' + v.getBigUint64(0, true).toString(16).padStart(16, '0');
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  if (process.argv[2] === '--cpm') {
    const [nr, nc] = process.argv.slice(3, 5).map(Number);
    const args = process.argv.slice(5).map(Number);
    assert.equal(args.length, nr*nc + nc);
    console.log(artifactCPM(nr, nc, args.slice(0, nr*nc), args.slice(nr*nc)).join('\n'));
  } else {
    const c = 2 ** 1023;
    const overflow = artifactCPM(1, 1, [c], [c])[0];
    assert.equal(bits(c), '0x7fe0000000000000');
    assert.equal(bits(overflow), '0x7ff0000000000000');
    assert.equal((c/c)*1e6, 1000000);
    console.log(`R1: c=L=2^1023; artifact=${overflow} (${bits(overflow)}); target=1000000 exactly`);
    const raw = artifactCPM(1, 2, [10, 10], [18, 18]);
    const cutoff = 10/18*1e6;
    assert(raw.every(x => bits(x) === '0x4120f4471c71c71c'));
    assert.equal(bits(cutoff), '0x4120f4471c71c71d');
    assert.equal(bits(10/18), '0x3fe1c71c71c71c72');
    assert(raw.every(x => x < cutoff));
    console.log(`R2: counts=[10,10], lib.size=[18,18]; artifact=${raw[0]} (${bits(raw[0])}); cutoff=${cutoff} (${bits(cutoff)})`);
    console.log('ARTIFACT COUNTEREXAMPLES PASS');
  }
}
