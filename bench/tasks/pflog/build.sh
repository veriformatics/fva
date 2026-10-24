#!/usr/bin/env bash
# How runorm-pflog.wasm was built (Rust 1.99.1, target wasm32-unknown-unknown; not needed to
# verify the artifact). shim/Cargo.toml depends on the crate in shim/vendor/runorm/.
set -euo pipefail
cd shim
RUSTFLAGS='-C target-cpu=generic -C target-feature=-simd128,-relaxed-simd -C link-arg=--no-entry
-C link-arg=--export-memory -C link-arg=-z -C link-arg=stack-size=65536' \
	cargo build --release --locked --target wasm32-unknown-unknown
cp target/wasm32-unknown-unknown/release/fva_runorm.wasm ../runorm-pflog.wasm
