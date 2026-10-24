# LZ4 block decoder in C (WebAssembly build)

`lz4-c.wasm` is the WebAssembly build (8,469 bytes, sha256 `8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6`) of `src/lz4.c` from lz4 v1.10.0, unmodified. `build.sh` records how it was built; `src/c-memory.c` supplies `memcpy`, `memmove` and `memset`, because the build has no C library. The module is the artifact to verify. The official documentation of the format is `lz4_Block_format.md`.

## Interface

The module exports its memory (2 MiB, fixed size) and two functions. All values are `i32`, and addresses are byte offsets in the exported memory. The module keeps its stack and data below address 131072, so the caller places buffers at addresses 131072 to 2097151.

- `LZ4_decompress_safe(src, dst, srcSize, dstCapacity)` decodes the block of `srcSize` bytes at `src` into the buffer of `dstCapacity` bytes at `dst`, as `src/lz4.h` documents it (the comment above its declaration).
- `LZ4_compress_default(src, dst, srcSize, dstCapacity)` encodes a block. It is not part of the requirements.

## Requirements

In each requirement, `srcSize` and `dstCapacity` are non-negative, and both buffers lie at addresses 131072 to 2097151.

- R1: `LZ4_decompress_safe` reads no byte outside `src[0 .. srcSize)` and writes no byte outside `dst[0 .. dstCapacity)` at those addresses, whatever the bytes at `src` are.
- R2: If the `srcSize` bytes at `src` are a valid block of the LZ4 block format, as `lz4_Block_format.md` defines it, and its decoded content fits in `dstCapacity` bytes, then `LZ4_decompress_safe` writes exactly that content at `dst` and returns its length.
- R3: If `LZ4_decompress_safe` returns a value `r` that is not negative, then `r ≤ dstCapacity`, the `srcSize` bytes at `src` are a sequence of LZ4 sequences as the format defines them, and `r` and the `r` bytes written at `dst` are their decoded length and content. A block that breaks only the end-of-block conditions may decode, because the format allows a decoder to accept it.
