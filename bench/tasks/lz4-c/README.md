# LZ4 block decoder in C (WebAssembly build)

`lz4-c.wasm` is the WebAssembly build (8,469 bytes, sha256 `8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6`) of `src/lz4.c` from lz4 v1.10.0, unmodified. `build.sh` records how it was built; `src/c-memory.c` supplies `memcpy`, `memmove` and `memset`, because the build has no C library. The module is the artifact to verify. The official documentation of the format is `lz4_Block_format.md`.

## Interface

The module exports its memory (2 MiB, fixed size) and two functions. All values are `i32`, and addresses are byte offsets in the exported memory. The module keeps its stack and data below address 131072, so the caller places buffers at addresses 131072 to 2097151.

- `LZ4_decompress_safe(src, dst, srcSize, dstCapacity)` decodes the block of `srcSize` bytes at `src` into the buffer of `dstCapacity` bytes at `dst`, as `src/lz4.h` documents it (the comment above its declaration).
- `LZ4_compress_default(src, dst, srcSize, dstCapacity)` encodes a block. It is not part of the requirements.

## Requirements

In each requirement, `srcSize` and `dstCapacity` are non-negative, the buffers `src[0 .. srcSize)` and `dst[0 .. dstCapacity)` do not overlap, and both lie at addresses 131072 to 2097151.

- R1: Among the addresses 131072 to 2097151, `LZ4_decompress_safe` reads only bytes of `src[0 .. srcSize)` and `dst[0 .. dstCapacity)`, and writes only bytes of `dst[0 .. dstCapacity)`, whatever the bytes at `src` are.
- R2: Let the `srcSize` bytes at `src` be a valid independent block of the LZ4 block format, as `lz4_Block_format.md` defines it: a block whose matches refer only to bytes already decoded from this block (`LZ4_decompress_safe` takes no dictionary and no previous block). Let its decoded content fit in `dstCapacity` bytes, where `dstCapacity` is at least 1 or the block is the single byte 0. Then `LZ4_decompress_safe` returns the length `r` of the decoded content, and afterwards `dst[0 .. r)` holds that content. The capacity condition is specific to this implementation: with zero output capacity, it accepts only the one-byte block 0, which the format names as the representation of empty input.
- R3: If `LZ4_decompress_safe` returns a value `r` that is not negative, then `r ≤ dstCapacity`, the `srcSize` bytes at `src` split into LZ4 sequences as the format defines them, each match offset at most the number of bytes decoded before that match, and `dst[0 .. r)` holds their decoded content, of length `r`. Two departures from the format's rules are allowed. A block that breaks only the end-of-block conditions may decode, because the format allows a decoder to accept it. A match offset may be 0: the format calls such a block invalid, and its section "Safe decoding" says that the reference decoder, which this is, decodes such a match as `matchlength` bytes of value 0.
