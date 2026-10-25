'use strict';
const fs = require('node:fs');
const assert = require('node:assert/strict');
(async () => {
  const c = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
  const bytes = fs.readFileSync('lz4-block-codec.wasm');
  const {instance: {exports: e}} = await WebAssembly.instantiate(bytes);
  assert.equal(e.memory.buffer.byteLength, 65536);
  assert.equal(e.getLinearMemoryOffset(), 0);
  let m = new Uint8Array(e.memory.buffer);
  // Valid nonempty block; disjoint, fully allocated input and output.
  const valid = Buffer.from(c.validHex, 'hex');
  const decoded = Buffer.from(c.decodedText);
  m.set(valid, 1024);
  assert.equal(e.lz4BlockDecode(1024, valid.length, 0), 1);
  assert.equal(m[0], 65);
  assert.equal(e.lz4BlockDecode(1024, valid.length, 2048), decoded.length);
  assert.deepEqual(Buffer.from(m.slice(2048, 2048 + decoded.length)), decoded);
  // Changing only the bytes outside a valid [0] block changes the result.
  m[1024] = 0; m[1026] = 0; m[2047] = 65;
  for (const [outside, result] of [[0, 0], [1, 4]]) {
    m[1025] = outside;
    m.fill(0, 2048, 2052);
    assert.equal(e.lz4BlockDecode(1024, 1, 2048), result);
    assert.deepEqual([...m.slice(2048, 2052)], Array(4).fill(outside ? 65 : 0));
  }
  // [0] is a valid empty block. No output space is needed.
  m[65535] = 0;
  assert.throws(() => e.lz4BlockDecode(65535, 1, 0),
    err => err instanceof WebAssembly.RuntimeError && /memory access out of bounds/.test(err.message));
  // Encoder's documented initialization, followed by disjoint buffers.
  e.memory.grow(5);
  m = new Uint8Array(e.memory.buffer);
  new Int32Array(e.memory.buffer, 0, 65536).fill(-65536);
  const input = Buffer.from(c.encodeInput);
  m.set(input, 262144);
  const expected = Buffer.from(c.encodedHex, 'hex');
  const n = e.lz4BlockEncode(262144, input.length, 300000);
  assert.equal(n, expected.length);
  assert.deepEqual(Buffer.from(m.slice(300000, 300000 + n)), expected);
  assert.deepEqual(Buffer.from(m.slice(262144, 262144 + input.length)), input);
  console.log('V8: R1 invalid block, R2 wrong length 1 (expected 13), R3 out-of-bounds trap reproduced');
})().catch(err => { console.error(err); process.exitCode = 1; });
