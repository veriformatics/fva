#!/usr/bin/env bash
# How lz4-flex.wasm was built (Rust 1.99.1, target wasm32-unknown-unknown; not needed to verify
# the artifact). shim/Cargo.toml depends on the crate in shim/vendor/lz4_flex/.
set -euo pipefail
cd shim
RUSTFLAGS='-C target-cpu=generic -C target-feature=-simd128,-relaxed-simd -C link-arg=--no-entry
-C link-arg=--export-memory -C link-arg=--initial-memory=2097152
-C link-arg=--max-memory=2097152 -C link-arg=-z -C link-arg=stack-size=65536' \
	cargo build --release --frozen --target wasm32-unknown-unknown
cp target/wasm32-unknown-unknown/release/fva_lz4_flex.wasm ../lz4-flex.wasm
