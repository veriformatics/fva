import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';

const bytes = readFileSync('lz4-block-codec.wasm');
const digest = createHash('sha256').update(bytes).digest('hex');
assert.equal(bytes.length, 1226);
assert.equal(digest, '4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf');
const exported = spawnSync('lake', ['env', 'lean', '--run', 'ExportWitnesses.lean'], { encoding: 'utf8' });
assert.equal(exported.status, 0, exported.stderr + exported.stdout);
const w = JSON.parse(exported.stdout);
const module = new WebAssembly.Module(bytes);
const fresh = () => new WebAssembly.Instance(module).exports;
const view = e => new Uint8Array(e.memory.buffer);
const slice = (e, ptr, n) => Array.from(view(e).slice(ptr, ptr + n));
console.log(`Artifact: ${bytes.length} bytes, sha256 ${digest}`);

// R1: initialize every hash word exactly as the README requires. All buffers
// are disjoint, after the table, and have enough space in grown memory.
{
  const e = fresh();
  e.memory.grow(7);
  const table = e.getLinearMemoryOffset();
  assert.equal(table, 0);
  new Int32Array(e.memory.buffer, table, 65536).fill(-65536);
  const input = 262144, output = 327680;
  view(e).set(w.encoderInput, input);
  const bound = e.lz4BlockEncodeBound(w.encoderInput.length);
  assert.ok(output + bound <= e.memory.buffer.byteLength);
  const n = e.lz4BlockEncode(input, w.encoderInput.length, output);
  assert.equal(n, w.encoderBlock.length);
  assert.deepEqual(slice(e, output, n), w.encoderBlock);
  console.log(`R1 FAIL confirmed: encode(${input}, 13, ${output}) returns ${n}; bytes ${Buffer.from(w.encoderBlock).toString('hex')}; Lean proves invalid.`);
}

// R2: a valid independent block. Repeat with output on each side of input.
for (const output of [0, 2048]) {
  const e = fresh();
  view(e).set(w.decoderBlock, 1024);
  view(e).fill(0xcc, output, output + w.decoderContent.length);
  const n = e.lz4BlockDecode(1024, w.decoderBlock.length, output);
  if (output === 0) {
    assert.equal(n, 1);
    assert.equal(view(e)[output], 65);
    assert.deepEqual(slice(e, output + 1, 12), Array(12).fill(0xcc));
    assert.notEqual(n, w.decoderContent.length);
    console.log('R2 FAIL confirmed: decode(1024, 10, 0) returns 1 and writes only 41; valid block requires 13 bytes 41414141414141414243444546.');
  } else {
    assert.equal(n, w.decoderContent.length);
    assert.deepEqual(slice(e, output, n), w.decoderContent);
    console.log('R2 control: decode(1024, 10, 2048) returns the expected 13 bytes.');
  }
}

// R3: the valid empty block fits exactly at the end of the initial memory.
// There are no output writes to perform. A memory access trap therefore
// exposes an out-of-block read, not an undersized output allocation.
{
  const e = fresh();
  assert.equal(e.memory.buffer.byteLength, 65536);
  view(e).set(w.emptyBlock, 65535);
  let trapped = false;
  try { e.lz4BlockDecode(65535, 1, 0); }
  catch (error) {
    assert.ok(error instanceof WebAssembly.RuntimeError);
    assert.match(error.message, /memory access out of bounds/i);
    trapped = true;
    console.log(`R3 FAIL confirmed: decode(65535, 1, 0) traps: ${error.message}`);
  }
  assert.ok(trapped, 'Expected an out-of-bounds memory read for the valid empty block');
}
console.log('PASS: all three counterexamples reproduced against the pinned shipped artifact.');
