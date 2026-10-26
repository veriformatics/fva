// Execute the unmodified shared module. Only calloc/free are used by this call.
import fs from 'node:fs';
const [rows, cols] = process.argv.slice(2, 4).map(Number);
const [input, output] = process.argv.slice(4);
if (!(rows > 0 && cols > 0 && Number.isInteger(rows) && Number.isInteger(cols)))
  throw Error('invalid dimensions');
const data = fs.readFileSync(input);
if (data.length !== 8 * (rows * cols + cols)) throw Error('invalid input length');
const memory = new WebAssembly.Memory({initial: 16});
const table = new WebAssembly.Table({initial: 9, element: 'anyfunc'});
let heap = 131136;
function calloc(n, size) {
  const p = heap;
  heap = (heap + n * size + 7) & ~7;
  if (heap > memory.buffer.byteLength) throw Error('out of memory');
  new Uint8Array(memory.buffer, p, heap - p).fill(0);
  return p;
}
const mod = new WebAssembly.Module(fs.readFileSync('edgeR.so'));
const imports = {};
for (const {module, name, kind} of WebAssembly.Module.imports(mod)) {
  const ns = imports[module] ??= {};
  if (kind === 'function') {
    ns[name] = name === 'R_chk_calloc' ? calloc : name === 'R_chk_free' ? () => {} :
      () => { throw Error(`unexpected import called: ${module}.${name}`); };
  } else if (kind === 'memory') ns[name] = memory;
  else if (kind === 'table') ns[name] = table;
  else if (kind === 'global') ns[name] = new WebAssembly.Global({value: 'i32',
    mutable: name === '__stack_pointer' || module.startsWith('GOT.')},
    name === '__stack_pointer' ? 65536 : 0);
  else throw Error(`unsupported import: ${kind}`);
}
const instance = new WebAssembly.Instance(mod, imports);
const counts = calloc(rows * cols, 8), libs = calloc(cols, 8);
new Uint8Array(memory.buffer, counts, data.length).set(data);
const view = new DataView(memory.buffer);
// cmx = {dmat, imat, nrow, ncol, type, isint, pnrow, rowsel}, wasm32.
for (const [p, ptr, type] of [[131072, counts, 0], [131104, libs, 2]]) {
  [ptr, 0, rows, cols, type, 0, rows, 0].forEach((v, i) => view.setInt32(p + 4*i, v, true));
}
instance.exports.calc_cpm_raw(131072, 131104, counts, 1);
fs.writeFileSync(output, new Uint8Array(memory.buffer, counts, rows * cols * 8));
