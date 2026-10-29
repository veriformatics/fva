// Direct tests of the unmodified, digest-pinned module in Node's Wasm engine.
import fs from 'node:fs';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';

const raw = fs.readFileSync('lz4-flex.wasm');
assert.equal(raw.length, 7161);
assert.equal(crypto.createHash('sha256').update(raw).digest('hex'),
  '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775');
const {exports: dut} = new WebAssembly.Instance(new WebAssembly.Module(raw));
const mem = new Uint8Array(dut.memory.buffer);
assert.equal(mem.length, 2097152);

// Independent slow parser; it intentionally does not enforce end conditions.
function reference(input, cap) {
  let p = 0;
  const out = [];
  function byte() {
    if (p === input.length) throw Error('truncated');
    return input[p++];
  }
  function length(n) {
    if (n === 15) {
      let b;
      do { b = byte(); n += b; } while (b === 255);
    }
    return n;
  }
  try {
    for (;;) {
      const token = byte(), literalLength = length(token >>> 4);
      if (p + literalLength > input.length || out.length + literalLength > cap) return null;
      out.push(...input.slice(p, p + literalLength));
      p += literalLength;
      if (p === input.length) return out;
      const offset = byte() + 256 * byte();
      const matchLength = length(token & 15) + 4;
      if (offset === 0 || offset > out.length || out.length + matchLength > cap) return null;
      for (let j = 0; j < matchLength; ++j) out.push(out[out.length - offset]);
    }
  } catch { return null; }
}

let count = 0;
function test(input, cap, src = 131072, dst = 262144, fullSnapshot = false, fixture = null) {
  assert(src >= 131072 && src + input.length <= mem.length);
  assert(dst >= 131072 && dst + cap <= mem.length);
  assert(src + input.length <= dst || dst + cap <= src);
  const low = Math.max(131072, dst - 32), high = Math.min(mem.length, dst + cap + 32);
  mem.fill(0, low, high);
  mem.fill(165, dst, dst + cap);
  mem.set(input, src);
  const before = fullSnapshot ? mem.slice() : mem.slice(low, high);
  const expected = reference(input, cap);
  const r = dut.lz4_decompress(src, dst, input.length, cap);
  assert.equal(r, expected === null ? -1 : expected.length,
    `return: input=${JSON.stringify(input)} cap=${cap}`);
  if (r >= 0) assert.deepEqual(Array.from(mem.slice(dst, dst + r)), expected);
  if (fixture) {
    assert.equal(r, fixture.result, fixture.name);
    if (r >= 0) assert.deepEqual(expected, fixture.output, fixture.name);
  }
  assert.deepEqual(Array.from(mem.slice(src, src + input.length)), input, 'source changed');
  if (fullSnapshot) {
    for (let a = 131072; a < mem.length; ++a) {
      if (a < dst || a >= dst + cap) assert.equal(mem[a], before[a], `outside write at ${a}`);
    }
  } else {
    for (let a = low; a < high; ++a) {
      if (a < dst || a >= dst + cap) assert.equal(mem[a], before[a - low], `guard at ${a}`);
    }
  }
  count++;
}

const cases = JSON.parse(fs.readFileSync('verification/cases.json', 'utf8'));
for (const c of cases) test(c.input, c.cap, c.src ?? 131072, c.dst ?? 262144, true, c);
console.log(`PASS: ${cases.length} fixtures on exact artifact, including full caller-region write snapshots`);

const capacities = [0, 1, 2, 4, 18, 34, 64];
for (const cap of capacities) {
  test([], cap);
  for (let a = 0; a < 256; ++a) test([a], cap);
  for (let a = 0; a < 256; ++a)
    for (let b = 0; b < 256; ++b) test([a, b], cap);
}
console.log('PASS: all 0-, 1-, and 2-byte inputs at capacities 0,1,2,4,18,34,64');

let seed = 0x4c5a34;
function random(n) {
  seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5;
  return (seed >>> 0) % n;
}
for (let j = 0; j < 5000; ++j) {
  const input = Array.from({length: random(101)}, () => random(256));
  test(input, random(257));
}
function ext(n) {
  if (n < 15) return [];
  n -= 15;
  return [...Array(Math.floor(n / 255)).fill(255), n % 255];
}
// Valid independent blocks: one or more matches and at least 12 final literals.
for (let j = 0; j < 1000; ++j) {
  const input = [];
  let decodedLength = 0;
  for (let k = 0; k <= j % 5; ++k) {
    const nl = 1 + random(36), ml = 4 + random(301);
    const literals = Array.from({length: nl}, () => random(256));
    const offset = 1 + random(Math.min(65535, decodedLength + nl));
    input.push(16 * Math.min(15, nl) + Math.min(15, ml - 4), ...ext(nl),
      ...literals, offset % 256, Math.floor(offset / 256), ...ext(ml - 4));
    decodedLength += nl + ml;
  }
  input.push(0xc0, ...Array.from({length: 12}, () => random(256)));
  decodedLength += 12;
  for (const cap of [decodedLength - 1, decodedLength, decodedLength + 64]) test(input, cap);
}
console.log(`PASS: ${count} total direct artifact executions; no counterexample found`);
