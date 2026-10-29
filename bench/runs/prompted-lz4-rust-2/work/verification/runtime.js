'use strict';
const fs = require('fs');
const assert = require('assert/strict');
const bytes = fs.readFileSync('lz4-flex.wasm');
const cases = JSON.parse(fs.readFileSync('verification/cases.json'));
(async () => {
  const module = await WebAssembly.compile(bytes);
  for (const c of cases) {
    const {exports: e} = await WebAssembly.instantiate(module);
    const m = new Uint8Array(e.memory.buffer);
    assert.equal(m.length, 2097152);
    m.fill(90, 131072);
    m.fill(165, c.dst, c.dst+c.cap);
    m.set(c.input, c.src);
    const r = e.lz4_decompress(c.src, c.dst, c.input.length, c.cap);
    assert.equal(r, c.expected === null ? -1 : c.expected.length, c.name);
    if (c.expected !== null)
      assert.deepEqual(Array.from(m.slice(c.dst, c.dst+r)), c.expected, c.name);
  }
  console.log(`V8: ${cases.length} original-artifact executions agree`);
})().catch(e => { console.error(e); process.exitCode=1; });
