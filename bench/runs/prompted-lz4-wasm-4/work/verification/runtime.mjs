import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';

// Execute the shipped bytes directly, with fresh memory for each witness.
const binary = readFileSync(new URL('../lz4-block-codec.wasm', import.meta.url));
const fresh = async () => (await WebAssembly.instantiate(binary)).instance.exports;
{
  const e = await fresh();
  assert.equal(e.getLinearMemoryOffset(), 0);
  assert.equal(e.memory.grow(7), 1);
  const words = new DataView(e.memory.buffer);
  for (let i = 0; i < 65536; i++) words.setInt32(i * 4, -65536, true);
  const memory = new Uint8Array(e.memory.buffer);
  memory.set(Buffer.from('abcdefabcdxyz'), 262144);
  const size = e.lz4BlockEncode(262144, 13, 300000);
  assert.equal(size, 13);
  assert.equal(Buffer.from(memory.slice(300000, 300000 + size)).toString('hex'),
    '6061626364656606003078797a');
  console.log('Node R1: size=13, block=6061626364656606003078797a');
}
{
  const e = await fresh();
  const memory = new Uint8Array(e.memory.buffer);
  memory.set([0x13, 97, 1, 0, 0x50, 97, 97, 97, 97, 97], 1024);
  memory.fill(204, 0, 13);
  const size = e.lz4BlockDecode(1024, 10, 0);
  assert.equal(size, 1);
  assert.equal(memory[0], 97);
  assert.deepEqual(Array.from(memory.slice(1, 13)), Array(12).fill(204));
  if (process.argv.includes('--false')) assert.equal(size, 13);
  console.log('Node R2: length=1, output=61; next twelve bytes untouched');
}
{
  const e = await fresh();
  const memory = new Uint8Array(e.memory.buffer);
  assert.equal(memory.length, 65536);
  memory[65535] = 0;
  assert.throws(() => e.lz4BlockDecode(65535, 1, 0),
    error => error instanceof WebAssembly.RuntimeError && /out of bounds/.test(error.message));
  console.log('Node R3: valid empty block at 65535 causes out-of-bounds trap');
}
