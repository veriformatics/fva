# LZ4 block codec (WebAssembly)

`lz4-block-codec.wasm` is a shipped WebAssembly module (1,226 bytes, sha256 `4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf`) that encodes and decodes the LZ4 block format "as per official documentation". `lz4-block-codec.wat` is its source, written by hand. The official documentation of the format is `lz4_Block_format.md`. The module is the artifact to verify.

## Interface

The module exports its memory and these functions (all values are `i32`; addresses are byte offsets in the exported memory, which the caller grows as needed):

- `getLinearMemoryOffset()` returns the first address the caller may use (0).
- `lz4BlockEncodeBound(n)` returns the largest number of bytes that encoding `n` bytes can produce (0 when `n` is too large).
- `lz4BlockEncode(input, n, output)` encodes the `n` bytes at address `input` into a block written at address `output` and returns the block's size, or 0 when it does not encode (inputs below 13 bytes and above the size limit are not encoded). The caller first fills the 65,536 4-byte words at address `getLinearMemoryOffset()` with the value −65536 (a hash table the encoder uses) and places the input after that table.
- `lz4BlockDecode(input, n, output)` decodes the block of `n` bytes at address `input` into address `output` and returns the number of bytes written.

## Requirements

- R1: Every block that `lz4BlockEncode` returns is a valid block of the LZ4 block format, as `lz4_Block_format.md` defines it, and decoding it gives back exactly the encoded input.
- R2: For every valid block of the LZ4 block format, `lz4BlockDecode` writes exactly the block's decoded content and returns its length.
- R3: `lz4BlockDecode` reads no byte outside the block it is given (the `n` bytes at `input`).
