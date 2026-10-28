// Direct shipped-artifact tests plus a separate access-instrumented execution.
// These finite checks are not universal proofs of R1, R2, or R3.
'use strict';
const fs = require('node:fs');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const path = require('node:path');
const originalBytes = fs.readFileSync(path.join(__dirname, '..', 'lz4-c.wasm'));
assert.equal(crypto.createHash('sha256').update(originalBytes).digest('hex'),
  '8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6');
const original = new WebAssembly.Instance(new WebAssembly.Module(originalBytes)).exports;
const checked = new WebAssembly.Instance(new WebAssembly.Module(
  fs.readFileSync(path.join(__dirname, 'instrumented.wasm')))).exports;
const memories = [original, checked].map(e => new Uint8Array(e.memory.buffer));
assert.equal(memories[0].length, 2097152);

// Independent, bytewise definition of the sequence semantics in the format.
// End restrictions are deliberately relaxed, as permitted by R3. Zero offsets
// append zeroes, as specified by R3. Missing mandatory extension bytes reject.
function reference(input, limit) {
  const out = [];
  let ip = 0;
  function length(base) {
    if (base !== 15) return base;
    let x;
    do {
      if (ip === input.length) throw new Error('missing extension');
      x = input[ip++]; base += x;
    } while (x === 255);
    return base;
  }
  try {
    while (ip < input.length) {
      const token = input[ip++], ll = length(token >>> 4);
      if (ip + ll > input.length || out.length + ll > limit) return null;
      for (let i = 0; i < ll; i++) out.push(input[ip++]);
      if (ip === input.length) return Uint8Array.from(out);
      if (ip + 2 > input.length) return null;
      const off = input[ip] + 256 * input[ip + 1]; ip += 2;
      const ml = length(token & 15) + 4;
      if (off > out.length || out.length + ml > limit) return null;
      for (let i = 0; i < ml; i++) out.push(off === 0 ? 0 : out[out.length - off]);
    }
  } catch (_) { return null; }
  // The zero-byte source is not a sequence (even for empty decoded content).
  return null;
}

let seed = 0x6c7a3404;
function random(n) {
  seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5;
  return (seed >>> 0) % n;
}
let count = 0, successes = 0, validCount = 0;
function test(input, capacity, expected = undefined, layout = count % 4) {
  input = Uint8Array.from(input);
  const s = layout === 0 ? 131072 : layout === 1 ? 2097152 - input.length : 262144;
  let d = layout === 0 ? 1048576 : layout === 1 ? 131072 :
    layout === 2 ? 2097152 - Math.max(capacity, 1) : 524289;
  assert(s >= 131072 && s + input.length <= 2097152);
  assert(d >= 131072 && d + capacity <= 2097152);
  assert(s + input.length <= d || d + capacity <= s);
  for (const m of memories) {
    m.fill(0xa5, Math.max(131072, d - 32), Math.min(2097152, d + capacity + 32));
    m.set(input, s);
  }
  checked.bounds(s, d, input.length, capacity);
  const r = original.LZ4_decompress_safe(s, d, input.length, capacity);
  let q;
  try { q = checked.LZ4_decompress_safe(s, d, input.length, capacity); }
  catch (e) { throw new Error(`access/trap: input=${Buffer.from(input).toString('hex')} cap=${capacity} s=${s} d=${d}: ${e}`); }
  assert.equal(q, r);
  assert.deepEqual(memories[0].slice(d, d + capacity), memories[1].slice(d, d + capacity));
  for (const m of memories) assert.deepEqual(m.slice(s, s + input.length), input);
  if (r >= 0) {
    successes++;
    assert(r <= capacity);
    const decoded = reference(input, capacity);
    assert(decoded !== null, `R3 parse: ${Buffer.from(input).toString('hex')}`);
    assert.equal(r, decoded.length);
    assert.deepEqual(memories[0].slice(d, d + r), decoded);
  }
  if (expected !== undefined) {
    validCount++;
    assert.equal(r, expected.length);
    assert.deepEqual(memories[0].slice(d, d + r), Uint8Array.from(expected));
  }
  count++;
}

function extension(length) {
  const out = [];
  while (length >= 255) { out.push(255); length -= 255; }
  out.push(length); return out;
}
function literals(bytes) {
  return [Math.min(bytes.length, 15) << 4,
    ...(bytes.length >= 15 ? extension(bytes.length - 15) : []), ...bytes];
}
function sequence(lit, off, ml) {
  return [(Math.min(lit.length, 15) << 4) | Math.min(ml - 4, 15),
    ...(lit.length >= 15 ? extension(lit.length - 15) : []), ...lit,
    off & 255, off >>> 8, ...(ml >= 19 ? extension(ml - 19) : [])];
}

// Every one- and two-byte source, across capacity-zero and positive paths.
test([], 0); test([], 1);
for (let a = 0; a < 256; a++) {
  for (const cap of [0, 1, 14, 32, 65]) test([a], cap);
  for (let b = 0; b < 256; b++) test([a, b], (a + b) % 67);
}
// Every short literal token, all low nibbles, all nearby output capacities.
for (let n = 0; n < 15; n++) for (let low = 0; low < 16; low++) {
  const payload = Array.from({length: n}, () => random(256));
  const bytes = [(n << 4) | low, ...payload];
  for (const cap of [0, Math.max(0, n - 1), n, n + 1, 32, 256])
    test(bytes, cap, cap >= n && (cap > 0 || bytes[0] === 0) ? payload : undefined);
}
// Literal extension boundaries and long literals, at exact and spare capacities.
for (const n of [15, 16, 269, 270, 271, 524, 525, 4096, 65535, 65536]) {
  const payload = Array.from({length: n}, () => random(256));
  const bytes = literals(payload);
  for (const cap of [n, n + 1, n + 64]) test(bytes, cap, payload);
  test(bytes, n - 1);
}
// Independent single-match blocks: last match starts >=12 decoded bytes before
// block end (ml>=7 plus 5 final literals), all offset-copy cases, extensions.
for (const off of [1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 31, 255, 256, 65535]) {
  for (const ml of [7, 8, 12, 18, 19, 20, 273, 274, 275, 1024]) {
    const lit = Array.from({length: off}, () => random(256));
    const tail = Array.from({length: 5}, () => random(256));
    const bytes = [...sequence(lit, off, ml), ...literals(tail)];
    const out = [...lit];
    for (let i = 0; i < ml; i++) out.push(out[out.length - off]);
    out.push(...tail);
    for (const cap of [out.length, out.length + 64]) test(bytes, cap, out);
    test(bytes, out.length - 1);
  }
}
// Zero offsets are invalid-format inputs, tested under R3's explicit exception.
for (const ml of [4, 7, 8, 18, 19, 274, 1024]) {
  const bytes = [...sequence([], 0, ml), ...literals([1, 2, 3, 4, 5])];
  const cap = ml + 5;
  test(bytes, cap); test(bytes, cap + 64);
}
// Chained matches, then bounded malformed-input fuzzing.
for (let trial = 0; trial < 2000; trial++) {
  const bytes = [], output = [];
  for (let j = 0; j < 1 + random(8); j++) {
    const lit = Array.from({length: 1 + random(40)}, () => random(256));
    output.push(...lit);
    const off = 1 + random(Math.min(output.length, 65535));
    const ml = 7 + random(400);
    bytes.push(...sequence(lit, off, ml));
    for (let i = 0; i < ml; i++) output.push(output[output.length - off]);
  }
  const tail = Array.from({length: 5 + random(25)}, () => random(256));
  bytes.push(...literals(tail)); output.push(...tail);
  test(bytes, output.length + random(80), output);
  const mutant = bytes.slice(); mutant[random(mutant.length)] = random(256);
  test(mutant, output.length + 80);
}
for (let trial = 0; trial < 10000; trial++) {
  const input = Array.from({length: random(512)}, () => random(256));
  test(input, random(2048));
}
console.log(`PASS: ${count} artifact executions; ${validCount} valid-block cases; ${successes} nonnegative results checked against sequence semantics; instrumented access checks passed`);
