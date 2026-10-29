#!/usr/bin/env bash
# Reproduce without overwriting the artifact or using the network.
set -euo pipefail
cd "$(dirname "$0")/.."
rust_bin="${RUST_TOOLCHAIN_BIN:-/home/eturkes/.cache/fva-bench/tools/rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/bin}"
rebuild_tmp="$(mktemp -d)"
trap 'rm -rf "$rebuild_tmp"' EXIT
(
  cd shim
  RUSTC="$rust_bin/rustc" \
  CARGO_HOME="$rebuild_tmp/cargo" \
  CARGO_TARGET_DIR="$rebuild_tmp/target" \
  RUSTFLAGS='-C target-cpu=generic -C target-feature=-simd128,-relaxed-simd -C link-arg=--no-entry -C link-arg=--export-memory -C link-arg=--initial-memory=2097152 -C link-arg=--max-memory=2097152 -C link-arg=-z -C link-arg=stack-size=65536' \
    "$rust_bin/cargo" build --release --frozen --offline --target wasm32-unknown-unknown
)
cmp lz4-flex.wasm "$rebuild_tmp/target/wasm32-unknown-unknown/release/fva_lz4_flex.wasm"
sha256sum lz4-flex.wasm
printf '%s\n' 'PASS: rebuild is byte-identical to the shipped artifact'
