#!/usr/bin/env bash
# How lz4-c.wasm was built (WASI SDK 34.0 clang 23.1.0; not needed to verify the artifact).
set -euo pipefail
clang --target=wasm32-unknown-unknown -mcpu=generic -mno-simd128 -mno-relaxed-simd \
	-O2 -nostdlib -ffreestanding -fno-builtin -fvisibility=hidden -DLZ4_FREESTANDING=1 \
	-DLZ4_memcpy=memcpy -DLZ4_memmove=memmove -DLZ4_memset=memset -include src/c-memory.h \
	-Wl,--no-entry -Wl,--strip-all -Wl,--export-memory \
	-Wl,--export=LZ4_compress_default -Wl,--export=LZ4_decompress_safe \
	-Wl,--initial-memory=2097152 -Wl,--max-memory=2097152 -Wl,-z,stack-size=65536 \
	src/lz4.c src/c-memory.c -o lz4-c.wasm
