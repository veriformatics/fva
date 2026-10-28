// Finite checks of the exact artifact and its access-instrumented copy. No proof claim.
import {readFileSync} from 'node:fs';
import assert from 'node:assert/strict';
const original = (await WebAssembly.instantiate(readFileSync('lz4-c.wasm'))).instance.exports;
const monitored = (await WebAssembly.instantiate(readFileSync('verification/monitored.wasm'))).instance.exports;
const M = 2097152;
function bytesEqual(a, b, message) {
  assert.equal(a.length, b.length, message);
  for (let i = 0; i < a.length; i++) assert.equal(a[i], b[i], message);
}
const memories = [original, monitored].map(e => new Uint8Array(e.memory.buffer));
assert.equal(memories[0].length, M);
assert.equal(WebAssembly.Module.imports(new WebAssembly.Module(readFileSync('lz4-c.wasm'))).length, 0);
let seed = 0x5eeda11, count = 0, r2 = 0, r3 = 0;
function rnd(n) { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return (seed >>> 0) % n; }
function parse(input, limit, strict = false) {
  let i = 0, out = [], matches = 0, lastStart = -1;
  function length(n) {
    if (n === 15) {
      let x;
      do { if (i >= input.length) throw 0; x = input[i++]; n += x; } while (x === 255);
    }
    return n;
  }
  try {
    while (i < input.length) {
      const token = input[i++], literals = length(token >>> 4);
      if (i + literals > input.length || out.length + literals > limit) return null;
      for (let j = 0; j < literals; j++) out.push(input[i++]);
      if (i === input.length) {
        if (strict && matches && (literals < 5 || out.length - lastStart < 12)) return null;
        return Uint8Array.from(out);
      }
      if (i + 2 > input.length) return null;
      const offset = input[i] + 256 * input[i+1]; i += 2;
      if (offset > out.length || (strict && offset === 0)) return null;
      const match = 4 + length(token & 15);
      if (out.length + match > limit) return null;
      lastStart = out.length; matches++;
      for (let j = 0; j < match; j++) out.push(offset === 0 ? 0 : out[out.length-offset]);
    }
  } catch (e) { if (e !== 0) throw e; }
  return null;
}
function check(packet, cap) {
  const size = packet.length, placement = count % 3;
  const src = placement === 1 && size ? M-size : 131072;
  const dst = placement === 1 ? 131072 : placement === 2 ? M-Math.max(cap, 1) : 1048576;
  assert(src + size <= dst || dst + cap <= src);
  for (const mem of memories) {
    mem.fill(0xa5, dst, dst+cap);
    mem.set(packet, src);
  }
  monitored.set_bounds(src, dst, size, cap);
  let a, b;
  try {
    a = original.LZ4_decompress_safe(src, dst, size, cap);
    b = monitored.LZ4_decompress_safe(src, dst, size, cap);
    assert.equal(a, b, 'instrumentation changed result');
    bytesEqual(memories[0].subarray(dst, dst+cap), memories[1].subarray(dst, dst+cap));
    if (a >= 0) {
      assert(a <= cap, 'R3 length bound');
      const expected = parse(packet, cap);
      assert(expected, 'R3: successful block has no sequence parsing');
      assert.equal(a, expected.length, 'R3 decoded length');
      bytesEqual(memories[0].subarray(dst, dst+a), expected, 'R3 decoded content');
      r3++;
    }
    const valid = parse(packet, M, true);
    if (valid && valid.length <= cap && (cap >= 1 || size === 1 && packet[0] === 0)) {
      assert.equal(a, valid.length, 'R2 decoded length');
      bytesEqual(memories[0].subarray(dst, dst+a), valid, 'R2 decoded content');
      r2++;
    }
  } catch (e) {
    throw new Error(JSON.stringify({src, dst, size, cap, packet: Buffer.from(packet).toString('hex'), a, b}), {cause: e});
  }
  count++;
  if (count % 100000 === 0) console.log(`Checked ${count} calls`);
}
function emitLength(out, n) { while (n >= 255) {out.push(255); n -= 255;} out.push(n); }
function sequence(out, literals, offset, match) {
  const ml = match === null ? 0 : match-4;
  out.push(Math.min(15, literals.length)*16 + Math.min(15, ml));
  if (literals.length >= 15) emitLength(out, literals.length-15);
  out.push(...literals);
  if (match !== null) {
    out.push(offset & 255, offset >>> 8);
    if (ml >= 15) emitLength(out, ml-15);
  }
}
for (const cap of [0, 1, 11, 32, 64]) check([], cap);
for (let x = 0; x < 256; x++)
  for (const cap of [0, 1, 11, 32, 64]) check([x], cap);
for (let x = 0; x < 65536; x++)
  for (const cap of [0, 1, 11, 32, 64]) check([x >>> 8, x & 255], cap);
// Exercise every small offset, overlap, zero offset, length extensions, and wild copies.
for (const offset of [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 31, 255, 256, 65535]) {
  for (const match of [4, 7, 8, 12, 16, 18, 19, 20, 270, 526, 4096]) {
    const packet = [], literals = Array.from({length: Math.max(1, offset)}, (_, i) => i & 255);
    sequence(packet, literals, offset, match);
    sequence(packet, Array.from({length:12}, (_, i) => 0xf0+i), 0, null);
    const n = literals.length + match + 12;
    for (const cap of [0, 1, n-1, n, n+1, n+32]) check(packet, cap);
  }
}
for (const n of [0, 1, 5, 14, 15, 16, 254, 255, 269, 270, 525, 4096, 32767]) {
  const packet = [];
  sequence(packet, Array.from({length:n}, () => rnd(256)), 0, null);
  for (const cap of new Set([0, Math.max(0,n-1), n, n+1, n+32])) check(packet, cap);
}
for (let k = 0; k < 3000; k++) {
  const packet = [], sequences = 1+rnd(5); let total = 0;
  for (let j = 0; j < sequences; j++) {
    const literals = Array.from({length: 1+rnd(280)}, () => rnd(256));
    total += literals.length;
    const match = 4+rnd(1200), offset = 1+rnd(Math.min(total, 65535));
    sequence(packet, literals, offset, match); total += match;
  }
  sequence(packet, Array.from({length:12+rnd(30)}, () => rnd(256)), 0, null);
  const valid = parse(packet, M, true); assert(valid);
  check(packet, valid.length); check(packet, valid.length+32);
  packet[rnd(packet.length)] = rnd(256);
  check(packet, valid.length+32);
}
for (let k = 0; k < 10000; k++) {
  check(Array.from({length:rnd(100)}, () => rnd(256)), rnd(257));
}
console.log(`Finite artifact checks: PASS (${count} calls; ${r2} R2 antecedents; ${r3} nonnegative returns)`);
console.log('Every tested decoder access was monitored; this is not an exhaustive proof of R1, R2, or R3.');
