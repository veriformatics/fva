// Run the unmodified module in V8; report final writes outside the caller's output too.
import fs from 'node:fs';
import assert from 'node:assert/strict';
const data = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const mod = await WebAssembly.compile(fs.readFileSync('lz4-flex.wasm'));
for (const c of data) {
  const {exports: e} = await WebAssembly.instantiate(mod);
  const mem = new Uint8Array(e.memory.buffer);
  mem.fill(204);
  mem.set(c.input, 131072);
  const before = mem.slice();
  const r = e.lz4_decompress(131072, 262144, c.input.length, c.cap) >>> 0;
  assert.equal(r, c.result);
  assert.deepEqual(Array.from(mem.slice(262144, 262144+c.output.length)), c.output);
  assert.deepEqual(mem.slice(131072, 262144), before.slice(131072, 262144));
  assert.deepEqual(mem.slice(262144+c.cap), before.slice(262144+c.cap));
}
console.log(`V8: ${data.length} artifact execution cases agree`);
