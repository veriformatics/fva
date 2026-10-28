// Runtime evidence only. There is no instrumentation or recompilation of the artifact.
const fs = require('fs');
const assert = require('assert/strict');

(async () => {
  const bytes = fs.readFileSync('lz4-c.wasm');
  const { instance } = await WebAssembly.instantiate(bytes);
  const mem = Buffer.from(instance.exports.memory.buffer);
  const tests = JSON.parse(fs.readFileSync('verification/cases.json', 'utf8'));
  for (const t of tests) {
    const {src, dst, cap, data, ret, output, name} = t;
    mem.fill(165, 131072);
    Buffer.from(data).copy(mem, src);
    const before = Buffer.from(mem);
    const actual = instance.exports.LZ4_decompress_safe(src, dst, data.length, cap);
    if (ret < 0) assert(actual < 0, `${name}: expected error, received ${actual}`);
    else assert.equal(actual, ret, `${name}: return`);
    assert(mem.subarray(131072, dst).equals(before.subarray(131072, dst)),
           `${name}: write before destination`);
    assert(mem.subarray(dst + cap).equals(before.subarray(dst + cap)),
           `${name}: write after destination`);
    if (ret >= 0) {
      assert(mem.subarray(dst, dst + ret).equals(Buffer.from(output)), `${name}: output`);
    }
  }
  console.log(`V8: ${tests.length} cases, returns, output and entire outside-destination memory: PASS`);
})().catch(e => { console.error(e); process.exit(1); });
