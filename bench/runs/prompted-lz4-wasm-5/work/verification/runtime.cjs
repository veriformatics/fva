// Independent runtime replay using V8; the module bytes are never transformed.
const fs = require('node:fs');
const assert = require('node:assert/strict');
const witness = JSON.parse(fs.readFileSync('.verification/witnesses.json'));
const bytes = fs.readFileSync('lz4-block-codec.wasm');
const module_ = new WebAssembly.Module(bytes);
const instance = () => new WebAssembly.Instance(module_).exports;
const e = instance();
let mem = new Uint8Array(e.memory.buffer);
const block = witness.decoderBlock;
const expected = witness.decoderContent;
mem.fill(0xcc, 1024, 1056);
mem.set(block, 4096);
const actualLength = e.lz4BlockDecode(4096, block.length, 1024);
assert.equal(actualLength, 1);
assert.deepEqual([...mem.slice(1024, 1037)], [97, ...Array(12).fill(0xcc)]);
// A placement control: the identical valid block works with output above input.
assert.equal(e.lz4BlockDecode(4096, block.length, 8192), 13);
assert.deepEqual([...mem.slice(8192, 8205)], expected);
mem[65535] = 0;
assert.throws(() => e.lz4BlockDecode(65535, 1, 1024), error => {
  assert(error instanceof WebAssembly.RuntimeError);
  assert.match(error.stack, /wasm-function\[3\]:0x32c/);
  fs.writeFileSync('.verification/r3-trace.txt', error.stack + '\n');
  return true;
});
e.memory.grow(5);
mem = new Uint8Array(e.memory.buffer);
assert.equal(e.getLinearMemoryOffset(), 0);
new Int32Array(e.memory.buffer, 0, 65536).fill(-65536);
const input = witness.encoderInput;
const encoded = witness.encoderBlock;
mem.set(input, 262144);
assert.equal(e.lz4BlockEncode(262144, input.length, 327680), encoded.length);
assert.deepEqual([...mem.slice(327680, 327693)], encoded);
assert.equal(e.lz4BlockDecode(327680, encoded.length, 350000), input.length);
assert.deepEqual([...mem.slice(350000, 350013)], input);
// A deliberate false execution claim must be rejected by this setup.
assert.throws(() => assert.equal(actualLength, 13),
  assert.AssertionError);
console.log('V8: R1 invalid end condition; R2 returns 1 instead of 13; R3 traps; negative control rejected');
