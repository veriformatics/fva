// Corroboration in a real WebAssembly engine; not part of the formal proof.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const {avg_floor: average} = new WebAssembly.Instance(
  new WebAssembly.Module(fs.readFileSync('avg_floor.wasm'))).exports;
const bound = 2147483648;
let count = 0;
function check(a, b) {
  const sum = a + b; // Exact: at most 33 signed bits, below Number's 53-bit limit.
  const unsigned = ((sum % (2 * bound)) + 2 * bound) % (2 * bound);
  const signed = unsigned < bound ? unsigned : unsigned - 2 * bound;
  const result = average(a, b);
  assert.equal(result, Math.floor(signed / 2));
  assert.equal(result === Math.floor(sum / 2), -bound <= sum && sum < bound);
  count++;
}
const edges = [-bound, -bound + 1, -1073741824, -3, -1, 0, 1, 3, 1073741824, bound - 2, bound - 1];
for (const a of edges) for (const b of edges) check(a, b);
let state = 0x12345678;
function next() {
  state = (Math.imul(state, 1664525) + 1013904223) | 0;
  return state;
}
for (let i = 0; i < 4096; i++) check(next(), next());
assert.equal(average(bound - 1, bound - 1), -1);
assert.equal(average(-bound, -bound), 0);
console.log(`WebAssembly runtime corroboration: ${count} input pairs passed the proven characterization.`);
