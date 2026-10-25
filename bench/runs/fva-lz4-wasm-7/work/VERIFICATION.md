# Verification of the shipped LZ4 codec

**R1, R2 and R3 all fail.** Each has a concrete counterexample proved using FVA's execution semantics of the shipped WebAssembly bytes. The counterexamples also reproduce in an independent WebAssembly runtime using `counterexamples.mjs`.

## Results and exact theorem statements

The following declarations are in [Proofs/Proof.lean](Proofs/Proof.lean):

```lean
theorem r1_counterexample_holds : r1_counterexample
theorem r2_counterexample_holds : r2_counterexample
theorem r3_counterexample_holds : r3_counterexample
```

All names are in namespace `Proofs`. Their exact claim definitions, in [Proofs/Spec.lean](Proofs/Spec.lean), are:

```lean
def r1_counterexample : Prop := ∀ H,
  CallReturns H encoderStore allocation.2 "lz4BlockEncode"
    [.i32 262144, .i32 13, .i32 300000]
    (fun s vs => vs = [.i32 13] ∧ memoryBytes s 300000 13 = encoded)

def r2_counterexample : Prop := ∀ H,
  CallReturns H decoderStore allocation.2 "lz4BlockDecode"
    [.i32 100, .i32 10, .i32 32]
    (fun s vs => vs = [.i32 1] ∧ memoryBytes s 32 13 = [65,0,0,0,0,0,0,0,0,0,0,0,0])

def r3_counterexample : Prop := ∀ H,
  CallTraps H allocation.1 allocation.2 "lz4BlockDecode"
    [.i32 65535, .i32 1, .i32 32] (fun _ => True)
```

`CallReturns` proves termination without a trap and the specified return values and final memory, for every execution under every host behavior `H`. `CallTraps` proves termination with a trap. These claims contain no execution-fuel assumption. The proofs obtain them from kernel-checked deterministic runs and FVA's `runDet_must` soundness theorem. Internal run bounds are 3000, 1000 and 100 steps respectively; successful finite runs establish the unbounded semantic claims above.

### R1: encoder emits an invalid block

Caller setup: grow the initial one-page memory by four pages (five pages total); initialize the 65,536 little-endian hash words at address 0 to −65536; put ASCII `abcdefghabcdx` at address 262144. Input and output buffers are disjoint and in bounds. Call:

```text
lz4BlockEncode(262144, 13, 300000)
```

The theorem proves a return value of **13** and these exact 13 output bytes:

```text
80 61 62 63 64 65 66 67 68 08 00 10 78
```

Interpretation under the bundled format document:

- `80`, followed by `61 … 68`: eight literals `abcdefgh`.
- `08 00`: offset 8; the low token nibble 0 specifies a four-byte match `abcd`.
- `10 78`: a final literal-only sequence containing just `x`.

The final sequence has one literal, although the decoded input is longer than five bytes. The last match starts at decoded position 8 of 13, only five bytes before the end. This violates end conditions 2 and 3 in [lz4_Block_format.md](lz4_Block_format.md). Thus R1's validity conjunct is false; disproving its round-trip conjunct is unnecessary. This counterexample does not assert that these bytes fail to reconstruct the input in every permissive decoder.

### R2: decoder returns a wrong length and content on a valid block

Put this ten-byte block at address 100 in a fresh instance:

```text
13 41 01 00 50 42 43 44 45 46
```

Its first sequence has literal `A`, offset 1, and match length `3 + 4 = 7`. The final sequence contains five literals `BCDEF`. Its decoded content is **`AAAAAAAABCDEF`**, length **13**. It satisfies all end conditions: five final literals and last match at position 1, exactly twelve bytes before the end. Offset 1 refers to already decoded data, with the permitted overlapping match copy.

Call `lz4BlockDecode(100, 10, 32)`. The output range `[32,45)` and input range `[100,110)` are disjoint, with ample memory. The theorem proves that the decoder returns **1**, leaving output bytes `41` followed by twelve zero bytes, instead of the required content and length.

The decoder compares the match pointer against the compressed input's end: the first match pointer is 32, which is less than 110, so it exits prematurely. No documented interface rule requires output to follow input.

### R3: decoder reads beyond a valid empty block

In a fresh one-page instance, byte 65535 is zero. The one-byte block `[00]` is the format's explicit encoding of empty content. Call:

```text
lz4BlockDecode(65535, 1, 32)
```

The theorem proves that the call **traps**. After consuming the zero-literal token at 65535, the decoder attempts to read an offset at 65536, outside both the supplied block `[65535,65536)` and the one-page memory. The decoder's zero-literal path skips its end-of-literals exit check. Output address 32 is valid; empty output requires no writes. Thus this is a read beyond the input, rather than an undersized output buffer. The same example also violates R2.

The formal R3 theorem states the trap outcome. Identifying the particular offending load uses the decoded function body (`Lifted.func3`) and the boundary placement above; no instrumented execution model is substituted for FVA's semantics.

## Connection to the artifact

The subject is exactly `lz4-block-codec.wasm`, **1226 bytes**, SHA-256:

```text
4bda6947a0498618552cba53ab3780745fd34cc1a0d84696e83a0547dcd68acf
```

[Proofs/Lifted.lean](Proofs/Lifted.lean) was generated by:

```sh
fva/.lake/build/bin/fva lift lz4-block-codec.wasm Proofs/Lifted.lean --ns Proofs.Lifted
```

It contains the complete byte numeral and the kernel-checked theorem `Proofs.Lifted.decode_eq : decode bytes len = .ok module`. FVA additionally compares the numeral, file length, file bytes, and regenerated lifting against the actual `.wasm` file. The proof invokes functions allocated from this decoded module, including its real helper functions. `allocation` is `allocModule {} Lifted.module [] [] []`; the module has no imports, initialization segments, globals or start function. `encoderStore` describes precisely the caller's legal memory growth and initialization; `decoderStore` writes the given block into the fresh allocation. The `.wat` source is not used as the proof subject.

The full LZ4 format has not been formalized here. The formal results establish the exact artifact behaviors above. Classification of the two small byte strings as invalid/valid follows the explicit field-by-field interpretation against the bundled format document. This is the small remaining intent-review obligation, rather than a claimed machine proof of a general LZ4 parser or round-trip specification.

## Reproduce, offline

From this directory:

```sh
./check-verification.sh
```

The script runs `lake build`, `wasm-tools validate`, and `node counterexamples.mjs`. It then copies FVA into a fresh directory under `/tmp`, points its Lake configuration at the already installed packages, rebuilds its executable outside the subject project, and runs:

```sh
"$audit_dir/.lake/build/bin/fva" trust . --spec-module Proofs.Spec --root-module Proofs --json > TRUST.json
```

No network is needed. Node is used only for the additional runtime reproduction. All formal results can be checked with the Lake build and FVA audit alone. Do not regenerate `Lifted.lean` as a substitute for auditing the existing file.

Success means exit status 0; a successful Lake build; three `R1/R2/R3 FAIL` runtime messages (these confirm the defects); and `FVA PASS: three artifact counterexamples; no audit issues.` The audit JSON must have `"verdict": "pass"`, `"issues": []`, three artifact attachments, a successful Wasm byte link, and accepted replay by `leanchecker` and `con-leche`. **FVA PASS certifies the counterexample claims, not satisfaction of R1–R3.**

The completed audit is saved in [TRUST.json](TRUST.json). It uses FVA rebuilt in `/tmp/lz4-fva-audit`, outside this project. Both replay kernels accepted; the review surface is `Proofs.Spec`, 29 code lines. FVA's canary policy allows its pinned known acceptances and declines; this is not a claim that every negative canary was rejected.

## What must be read and trusted

Project-specific semantic review:

| File | Size | Role |
| --- | ---: | --- |
| `Proofs/Spec.lean` | 58 physical lines, 2715 bytes; 29 FVA code lines | Exact caller states, inputs, outputs, and semantic claims. |
| `lz4_Block_format.md` | 244 lines, 10683 bytes | Format authority; review the token/length/offset rules and end conditions used above. |
| `README.md` | 18 lines, 1798 bytes | Interface preconditions and requirements being checked. |

The trust base also includes FVA's pinned Wasm and claim specifications (`fva/FVA/Spec`: 3606 lines, 161903 bytes), the Lean 4.35 kernel, its standard axioms (`propext`, `Classical.choice`, `Quot.sound`), the pinned Mathlib dependencies, the Lean compiler/toolchain, and FVA's byte-link, export, replay and canary orchestration. Independent `con-leche` replay supplements Lean's kernel. FVA checks its base source hashes against its compiled manifest. Neither proof uses `sorry`, a custom axiom, or `native_decide`.

The generated lifting is 67 lines/20377 bytes and the proof file is 69 lines/2474 bytes; their contents are kernel checked and artifact linked, so they need not be accepted as unchecked descriptions of the software. `Proofs.lean` is a one-line proof import. `check-verification.sh` is 39 lines/1300 bytes; read it to audit the reproduction procedure. `counterexamples.mjs` is 45 lines/2133 bytes; it and Node's Wasm engine are needed only for the supplementary runtime demonstration, not the formal conclusions. The `.wasm` artifact and requirements were left unchanged.
