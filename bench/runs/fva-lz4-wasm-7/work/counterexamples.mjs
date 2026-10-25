import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';

const bytes = readFileSync('lz4-block-codec.wasm');
assert.equal(bytes.length, 1226);
assert.equal(createHash('sha256').update(bytes).digest('hex'),
  '4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf');
const module = new WebAssembly.Module(bytes);
const fresh = () => new WebAssembly.Instance(module).exports;

{
  const e = fresh();
  assert.equal(e.memory.grow(4), 1);
  const mem = new Uint8Array(e.memory.buffer);
  const view = new DataView(e.memory.buffer);
  for (let i = 0; i < 65536; ++i) view.setInt32(4 * i, -65536, true);
  mem.set(Buffer.from('abcdefghabcdx', 'ascii'), 262144);
  const size = e.lz4BlockEncode(262144, 13, 300000);
  assert.equal(size, 13);
  const block = Array.from(mem.slice(300000, 300000 + size));
  assert.deepEqual(block, [128,97,98,99,100,101,102,103,104,8,0,16,120]);
  // 80 + eight literals + 08 00: length-four match starts at decoded position 8.
  // 10 78: only one final literal. Decoded size 13; last match starts 5 from end.
  assert.equal(block[11] >>> 4, 1);
  console.log('R1 FAIL: encoded hex 80616263646566676808001078; one final literal; last match 5 bytes from end.');
}
{
  const e = fresh();
  const mem = new Uint8Array(e.memory.buffer);
  // 13 41 01 00 = literal A + seven-byte offset-one match.
  // 50 42 43 44 45 46 = final five literals BCDEF.
  mem.set([19,65,1,0,80,66,67,68,69,70], 100);
  assert.equal(e.lz4BlockDecode(100, 10, 32), 1);
  assert.deepEqual(Array.from(mem.slice(32, 45)), [65,0,0,0,0,0,0,0,0,0,0,0,0]);
  console.log('R2 FAIL: valid hex 13410100504243444546; expected AAAAAAAABCDEF (13), returned 1.');
}
{
  const e = fresh();
  assert.equal(e.memory.buffer.byteLength, 65536);
  assert.equal(new Uint8Array(e.memory.buffer)[65535], 0);
  assert.throws(() => e.lz4BlockDecode(65535, 1, 32), WebAssembly.RuntimeError);
  console.log('R3 FAIL: valid empty block 00 at 65535 traps; offset load at 65536 exceeds block and memory.');
}
console.log('All three counterexamples reproduced on the exact shipped bytes.');
