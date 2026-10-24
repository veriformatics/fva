# LZ4 block decoder in Rust (WebAssembly build)

`lz4-flex.wasm` is the WebAssembly build (7,161 bytes, sha256 `1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775`) of the Rust crate lz4_flex 0.14.0 (in `shim/vendor/lz4_flex/`, unmodified), with the features `safe-encode`, `safe-decode` and `checked-decode`. The crate in `shim/` exports two of its functions to WebAssembly, and `build.sh` records how the module was built. The module is the artifact to verify. The official documentation of the format is `lz4_Block_format.md`.

## Interface

The module exports its memory (2 MiB, fixed size) and two functions. All values are `i32`, and addresses are byte offsets in the exported memory. The module keeps its stack and data below address 131072, so the caller places buffers at addresses 131072 to 2097151.

- `lz4_decompress(src, dst, n, cap)` decodes the block of `n` bytes at `src` into the buffer of `cap` bytes at `dst` with `lz4_flex::block::decompress_into`, and returns the number of bytes written, or -1 when the block is invalid or does not fit (`shim/src/lib.rs`).
- `lz4_compress(src, dst, n, cap)` encodes a block. It is not part of the requirements.

## Requirements

In each requirement, the two buffers do not overlap and both lie at addresses 131072 to 2097151.

- R1: `lz4_decompress` reads no byte outside `src[0 .. n)` and writes no byte outside `dst[0 .. cap)` at those addresses, whatever the bytes at `src` are.
- R2: If the `n` bytes at `src` are a valid block of the LZ4 block format, as `lz4_Block_format.md` defines it, and its decoded content fits in `cap` bytes, then `lz4_decompress` writes exactly that content at `dst` and returns its length.
- R3: If `lz4_decompress` returns a value `r` that is not negative, then `r ≤ cap`, the `n` bytes at `src` are a sequence of LZ4 sequences as the format defines them, and `r` and the `r` bytes written at `dst` are their decoded length and content. A block that breaks only the end-of-block conditions may decode, because the format allows a decoder to accept it.
