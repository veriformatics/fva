// Independent direct execution of the hash-pinned shipped bytes.
import fs from 'node:fs';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
const bytes = fs.readFileSync('lz4-flex.wasm');
assert.equal(bytes.length, 7161);
assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),
  '1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775');
const mod = new WebAssembly.Module(bytes);
const cases = JSON.parse(fs.readFileSync('verification/cases.json', 'utf8'));
assert.equal(cases.length, 570);
const instance = new WebAssembly.Instance(mod);
const {memory, lz4_decompress: decode} = instance.exports;
const mem = new Uint8Array(memory.buffer);
const pristine = mem.slice();
const before = new Uint8Array(mem.length);
let count = 0;
for (const c of cases) {
  mem.set(pristine);
  assert.equal(mem.length, 2097152);
  assert(c.src >= 131072 && c.src+c.input.length <= mem.length);
  assert(c.dst >= 131072 && c.dst+c.cap <= mem.length);
  assert(c.src+c.input.length <= c.dst || c.dst+c.cap <= c.src);
  mem.fill(170, c.dst, c.dst+c.cap);
  mem.set(c.input, c.src);
  before.set(mem);
  const ret = decode(c.src, c.dst, c.input.length, c.cap);
  assert.equal(ret >>> 0, c.modelResult, `case ${count}: model return`);
  assert.equal(ret, c.expected === null ? -1 : c.expected.length, `case ${count}: expected return`);
  if (ret >= 0) {
    assert(ret <= c.cap);
    assert.deepEqual(Array.from(mem.slice(c.dst, c.dst+ret)), c.expected);
  }
  assert.deepEqual(Array.from(mem.slice(c.dst, c.dst+c.cap)), c.modelOutput,
    `case ${count}: complete destination versus model (including wild stores)`);
  assert.equal(Buffer.compare(Buffer.from(mem.buffer, 0, c.dst), Buffer.from(before.buffer, 0, c.dst)), 0,
    `case ${count}: memory before destination changed`);
  assert.equal(Buffer.compare(Buffer.from(mem.buffer, c.dst+c.cap), Buffer.from(before.buffer, c.dst+c.cap)), 0,
    `case ${count}: memory after destination changed`);
  count++;
  if (count % 100 === 0) console.log(`Checked ${count}/${cases.length} runtime cases`);
}
console.log(`PASS: ${count} direct executions; returns, full destination memory, and unchanged memory outside destination`);
