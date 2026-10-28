import fs from 'node:fs';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';

const raw = fs.readFileSync('lz4-c.wasm');
const original = new WebAssembly.Instance(new WebAssembly.Module(raw)).exports;
const guarded = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync('verification/out/guarded.wasm'))).exports;
const memories = [original, guarded].map(e => new Uint8Array(e.memory.buffer));
const BASE = 131072, END = 2097152;
let count = 0, r2 = 0, r3 = 0, seed = 0x4c5a34;
function rand(n) { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return (seed >>> 0) % n; }

// Independent, deliberately slow format parser. End conditions may be omitted for R3.
function spec(input, strictEnd = false) {
  let p = 0, output = [], lastMatchStart = -1, sequences = 0;
  function length(n) {
    if (n !== 15) return n;
    let v;
    do { if (p === input.length) throw Error('truncated length'); v = input[p++]; n += v; } while (v === 255);
    return n;
  }
  try {
    while (p < input.length) {
      const token = input[p++], ll = length(token >>> 4);
      if (p + ll > input.length) return null;
      for (let i = 0; i < ll; i++) output.push(input[p++]); sequences++;
      if (p === input.length) {
        if (strictEnd && ((sequences > 1 && ll < 5) || (lastMatchStart >= 0 && output.length - lastMatchStart < 12))) return null;
        return output;
      }
      if (p + 2 > input.length) return null;
      const offset = input[p] + 256 * input[p + 1]; p += 2;
      if (offset > output.length || (strictEnd && offset === 0)) return null;
      const ml = length(token & 15) + 4;
      if (output.length + ml > END - BASE) return null; // test resource limit, not a format rule
      lastMatchStart = output.length;
      for (let i = 0; i < ml; i++) output.push(offset === 0 ? 0 : output[output.length - offset]);
    }
  } catch { return null; }
  return null;
}

const runtimeCases = [];
function check(input, cap, expected = null, layout = 0) {
  assert(input.length + cap + 64 < END - BASE);
  const src = layout === 1 ? END - Math.max(input.length, 1) : BASE + 32;
  const dst = layout === 2 ? END - Math.max(cap, 1) : (layout === 3 ? src + input.length : BASE + 8192);
  assert(src >= BASE && dst >= BASE && src + input.length <= END && dst + cap <= END);
  assert(src + input.length <= dst || dst + cap <= src);
  for (const a of memories) { a.fill(0xa5, src, src + input.length); a.fill(0xa5, dst, dst + cap); a.set(input, src); }
  guarded.set_bounds(src, dst, input.length, cap);
  const r = original.LZ4_decompress_safe(src, dst, input.length, cap);
  const g = guarded.LZ4_decompress_safe(src, dst, input.length, cap);
  assert.equal(g, r, `guard changed result on ${Buffer.from(input).toString('hex')}`);
  assert.deepEqual(memories[1].slice(dst, dst + cap), memories[0].slice(dst, dst + cap));
  assert.deepEqual([...memories[0].slice(src, src + input.length)], [...input]);
  if (r >= 0) {
    const decoded = spec(input);
    assert(decoded !== null, `R3 parse failed: ${Buffer.from(input).toString('hex')}`);
    assert(r <= cap); assert.equal(r, decoded.length);
    assert.deepEqual([...memories[0].slice(dst, dst + r)], decoded); r3++;
  }
  if (expected !== null) {
    assert.deepEqual(spec(input, true), expected, 'invalid R2 test generator');
    assert.equal(r, expected.length, `R2 length: ${Buffer.from(input).toString('hex')}, cap=${cap}`);
    assert.deepEqual([...memories[0].slice(dst, dst + r)], expected); r2++;
  }
  if (runtimeCases.length < 80 && ((expected !== null && r2 % 23 === 1) || count % 997 === 0 || (r >= 0 && expected === null && r3 % 401 === 0))) runtimeCases.push({input: [...input], cap, src, dst, r, output: r >= 0 ? [...memories[0].slice(dst, dst + r)] : []});
  count++;
}

// Boundary cases, all one-byte inputs, and empty inputs.
for (const cap of [0, 1, 4, 13, 32, 64, 257]) {
  check([], cap);
  for (let b = 0; b < 256; b++) check([b], cap, b === 0 ? [] : null);
}
// Independent literal-only valid blocks, including variable-length encodings.
function literal(bytes) {
  const out = [Math.min(15, bytes.length) << 4];
  if (bytes.length >= 15) { let n = bytes.length - 15; while (n >= 255) { out.push(255); n -= 255; } out.push(n); }
  return out.concat(bytes);
}
for (const n of [0,1,4,5,12,13,14,15,16,18,31,32,63,64,255,269,270,271,525,1024,4096]) {
  const data = Array.from({length:n}, () => rand(256));
  for (const extra of [0,1,32,64]) for (const layout of [0,1,2,3]) {
    const cap = n + extra;
    check(literal(data), cap, data, layout);
  }
}
// Valid matches: offsets 1..32, lengths including extension-byte boundaries.
for (let offset = 1; offset <= 32; offset++) for (const ml of [4,7,8,12,18,19,20,31,32,64,274,275,529]) {
  const prefix = Array.from({length:offset}, () => rand(256));
  const first = literal(prefix); first[0] |= Math.min(15, ml - 4);
  first.push(offset, 0);
  if (ml >= 19) { let n = ml - 19; while (n >= 255) { first.push(255); n -= 255; } first.push(n); }
  const tail = Array.from({length:Math.max(5, 12-ml)}, () => rand(256));
  const input = first.concat(literal(tail)), decoded = prefix.slice();
  for (let i = 0; i < ml; i++) decoded.push(decoded[decoded.length-offset]);
  decoded.push(...tail);
  for (const extra of [0,32]) check(input, decoded.length + extra, decoded, rand(4));
}
// Accepted zero offsets, short tail runs, and malformed/random blocks are R3/R1 tests.
for (let i = 0; i < 20000; i++) {
  const n = rand(96), input = Array.from({length:n}, () => rand(256));
  check(input, rand(257), null, rand(3));
}
for (let ll = 0; ll <= 14; ll++) for (let ml = 4; ml <= 18; ml++) for (let tail = 5; tail <= 14; tail++) {
  const input = [(ll << 4) | (ml - 4), ...Array(ll).fill(0x61), 0, 0, tail << 4, ...Array(tail).fill(0x62)];
  check(input, ll + ml + tail + rand(40));
}
// Exercise long match extensions and long literal copies near the fixed-memory limit.
{
  const n = 1950000, ml = n - 6, input = [0x1f, 0x61, 1, 0];
  let rest = ml - 19;
  while (rest >= 255) { input.push(255); rest -= 255; }
  input.push(rest, 0x50, ...Array(5).fill(0x62));
  check(input, n, [...Array(n-5).fill(0x61), ...Array(5).fill(0x62)]);
  const data = Array.from({length:900000}, (_, i) => i % 256);
  check(literal(data), data.length, data, 3);
}
// Replay a mixture of successful and failing calls under Wasmtime on the exact binary.
const hex = b => [...b].map(v => '\\' + v.toString(16).padStart(2, '0')).join('');
const wast = [`(module $artifact binary "${hex(raw)}")`, '(register "artifact" $artifact)', `(module $host
  (import "artifact" "memory" (memory 32 32))
  (import "artifact" "LZ4_decompress_safe" (func $decode (param i32 i32 i32 i32) (result i32)))
  (func (export "poke") (param i32 i32) local.get 0 local.get 1 i32.store8)
  (func (export "peek") (param i32) (result i32) local.get 0 i32.load8_u)
  (export "decode" (func $decode)))`];
for (const c of runtimeCases) {
  c.input.forEach((b,i) => wast.push(`(invoke $host "poke" (i32.const ${c.src+i}) (i32.const ${b}))`));
  wast.push(`(assert_return (invoke $host "decode" (i32.const ${c.src}) (i32.const ${c.dst}) (i32.const ${c.input.length}) (i32.const ${c.cap})) (i32.const ${c.r}))`);
  c.output.forEach((b,i) => wast.push(`(assert_return (invoke $host "peek" (i32.const ${c.dst+i})) (i32.const ${b}))`));
}
fs.writeFileSync('verification/out/runtime.wast', wast.join('\n'));
execFileSync('wasmtime', ['wast', '-C', 'cache=n', 'verification/out/runtime.wast'], {stdio:'inherit'});
// Deliberately lie to the guard: one disallowed read and one disallowed write.
memories[1][BASE] = 0;
guarded.set_bounds(BASE, BASE+8192, 0, 0);
assert.throws(() => guarded.LZ4_decompress_safe(BASE, BASE+8192, 1, 0), WebAssembly.RuntimeError);
memories[1].set([0x10, 0x61], BASE);
guarded.set_bounds(BASE, BASE+8192, 2, 0);
assert.throws(() => guarded.LZ4_decompress_safe(BASE, BASE+8192, 2, 1), WebAssembly.RuntimeError);
// A corrupted assertion must fail, so an inert/disabled runtime is detected.
fs.writeFileSync('verification/out/false.wast', '(module (func (export "zero") (result i32) i32.const 0))\n(assert_return (invoke "zero") (i32.const 1))\n');
let rejected = false;
try { execFileSync('wasmtime', ['wast', '-C', 'cache=n', 'verification/out/false.wast'], {stdio:'pipe'}); } catch (e) { assert.match(String(e.stderr), /expected|assert|mismatch/i); rejected = true; }
assert(rejected, 'Wasmtime accepted a false assertion');
console.log(`Runtime tests: ${count} R1 traces, ${r2} R2 cases, ${r3} R3 successes; Wasmtime replayed ${runtimeCases.length} calls; false assertion rejected`);
