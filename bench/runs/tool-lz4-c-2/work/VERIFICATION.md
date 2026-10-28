# Verification results

**This is a partial verification. R1, R2, and R3 are not established in full,
and no counterexample to them was found.** Passing the replay command below
does not certify the general decoder. The shipped files have not been changed.

## Requirement-by-requirement status

### R1 — permitted reads and writes

Proved for the restricted case `srcSize == 0 || dstCapacity == 0`.
The machine-checked statement is the ACSL contract of `f2_early` in
`verification/early.c`, with definitions in `verification/memory.h`:

```c
requires arena;
requires v0 == sb && v1 == db;
requires v2 == se-sb && v3 == de-db;
requires v2 == 0 || v3 == 0;
assigns \nothing;
ensures \result == ((v3 == 0 && v2 == 1 && mem[v0] == 0)
                    ? 0 : 4294967295);
```

Here `v0,v1,v2,v3` are the four exported arguments, represented as unsigned
32-bit words; `4294967295` is the exported signed result `-1`.
`arena` means

```text
131072 <= sb <= se <= 2097152
131072 <= db <= de <= 2097152
sb == se OR db == de OR se <= db OR de <= sb
```

`mem` is a 2 MiB byte array. Each executed load must satisfy an explicit
precondition: its entire range lies in `[sb,se)` or `[db,de)`. Each store
must lie entirely in `[db,de)`. WP checks the calls' preconditions, not just
the postcondition. In this subcase there are no stores and at most one byte
load: `[sb]` when `dstCapacity == 0 && srcSize == 1`.

The assertion `unreachable_suffix: \false` is also proved. It establishes
that the rest of the decoder cannot be reached under the extra hypothesis;
the omitted suffix is not assumed correct. The combined check of this
prefix and the memory primitive implementations discharged **67/67 goals**,
including runtime-error checks.

The general R1 proof is incomplete. `verification/lifted.c` contains the
whole decoder and its copy callees, with candidate invariants in
`verification/annotations.json`. These annotations are proof attempts,
not established facts. In particular, a proof of the whole decoder's access
preconditions and all its loop invariants has not completed. Proving the
prefix, memory primitives, or copy callees alone does not prove general R1.

### R2 — correct decoding of valid independent blocks

The prefix theorem proves the zero-capacity empty-block case: for the block
`00`, with `srcSize = 1` and `dstCapacity = 0`, the result is `0`, no bytes
are written, and the decoded content is the empty byte string. This is the
explicit empty-input representation in the supplied format document.

**General R2 is unproved.** There is no machine-checked simulation between
the complete decoder and a formal LZ4 sequence semantics. The executable
reference decoder and valid-block generator in `verification/test.mjs` are
finite testing tools, not such a proof.

### R3 — meaning of successful returns

Under `srcSize == 0 || dstCapacity == 0`, the prefix theorem proves that the
only nonnegative return occurs for `srcSize = 1`, `dstCapacity = 0`, and
source byte `00`. It returns `0`, which is within capacity, and the source
is precisely the valid empty block with empty decoded content.

**General R3 is unproved.** The WP postcondition attempted on the full
decoder only states the numerical return bound; even proving that would
not establish source parsing, offsets, or decoded content. No general
format/content postcondition is claimed. In particular, the offset-zero
exception is tested, not proved for all match lengths and contexts.

## Connection to the shipped artifact

The artifact is the existing 8,469-byte `lz4-c.wasm`, SHA-256:

```text
8b73efb63f0467d9999d867007969b75826140dce9e5677bd0439dc6af384ac6
```

`verification/lift.py` checks that exact hash before reading the artifact
with `wasm-tools print`. It checks the memory declaration, decoder export,
and complete initialized data segment. It translates function 2 (the
decoder) and functions 3 and 4 (its copy callees) to unsigned-word C.
It rejects unsupported instructions. Operand-stack values are saved before
local-variable updates; WebAssembly branches become block exits or loop
back edges. Effective addresses use 64-bit addition of the 32-bit base
and immediate offset, so an offset cannot silently wrap before a load.

The generator also extracts `early.c` from the translated function's exact
early-return prefix. The omitted suffix is guarded by the proved false
assertion described above. Thus the completed theorem is about a model
extracted from these bytes, rather than about recompiling `src/lz4.c`.
**The lifting implementation is trusted; its semantic preservation has not
itself been formally proved.** The result is conditional on that translation
being faithful and on the memory primitives' correspondence to Wasm access
semantics. It is not an independently kernel-checked theorem about a formal
WebAssembly semantics.

`memory.c` implements byte loads/stores and little-endian 16-bit loads.
The 32-bit loads in this decoder are reads of the two static tables, modeled
by their exact initialized constants; `lift.py` checks those constants
against the data segment. This modeling assumes the caller preserves the
module's private data below 131072. This assumption is unnecessary for the
proved prefix, which performs no table loads. Load contracts conservatively
omit content information except for byte loads and the fixed tables; store
contracts give their write ranges. Their implementations are checked by WP.

Arithmetic normalization in the lifter replaces masks `&3`, `&15`, and
`&0xfffffffc` by remainder operations, fixed shifts by powers of two,
complement by subtraction from `0xffffffff`, and signed comparison with
zero by testing the sign-bit boundary. These translation identities are
part of the trusted implementation, not separate WP theorems.

The deterministic execution suite checks the original binary, an
instrumented version of it, and a compiled version of the C lift. All
**12,088 cases** passed: **546 valid-block R2 checks**, **710 successful
returns checked against the R3 reference semantics**, agreement of return
values and the entire destination buffer between all three executions,
unchanged source bytes, and no forbidden access in the instrumented binary.
Inputs include truncated/random blocks, literal-length extensions,
overlapping matches, offsets 0–9 and several larger offsets up to 65535,
match-length extensions, undersized destinations, and buffers at both ends
of the caller area. These results are finite observations, not universal
proofs. The instrumentation itself is trusted for these observations.

## Replaying completed results

Run from this directory, without network access:

```sh
bash verification/check.sh
```

The script runs the following exact commands:

```sh
python3 verification/lift.py
wasm-tools validate lz4-c.wasm
frama-c --check-wp . verification/early.c verification/memory.c \
  -wp -wp-rte -wp-prover qed,alt-ergo -wp-timeout 5
clang --target=wasm32 -O2 -nostdlib -ffreestanding -fno-builtin \
  -DLIFT_RUNTIME -Wl,--no-entry -Wl,--export-memory \
  -Wl,--export=f2 -Wl,--export=getmem \
  verification/lifted.c verification/memory.c -o verification/lifted.wasm
python3 verification/instrument.py
node verification/test.mjs
```

Success means exit status 0, WP reports **67/67 goals proved**, and the
execution suite prints:

```text
PASS: 12088 cases; 546 R2 checks; 710 successful returns checked for R3; guarded accesses and lifted execution agree.
```

`--check-wp` checks all goals selected in that invocation. No proof-property
filter, admitted goal, custom axiom, or `assume false` is used for the
completed prefix theorem. WP's notes about skipped alignment/function-pointer
guards do not hide accesses here: the model uses a global byte array,
integer indices, and direct calls, with no unaligned typed dereferences or
function-pointer calls.

To attempt the unfinished general proof separately:

```sh
frama-c --check-wp . verification/lifted.c verification/memory.c \
  -wp -wp-rte -wp-prover qed,alt-ergo -wp-timeout 5
```

This is **not** part of the passing replay and is **not** claimed to pass.
Proof generation for the complete decoder has been costly; unresolved or
timed-out goals mean unknown, not a demonstrated software failure.

## Review and trust inventory

Besides Frama-C 33.0/WP, its C/ACSL semantics and Qed simplifier, Alt-Ergo
2.5.4, Python, and `wasm-tools`' binary reader/printer, review these files.
Sizes are lines / bytes; the sizes include comments and blank lines.

| File | Size | Role |
| --- | ---: | --- |
| `verification/lift.py` | 190 / 7975 | Trusted byte-to-C translation and prefix extraction |
| `verification/memory.h` | 57 / 1673 | Memory model, access predicates, primitive contracts |
| `verification/memory.c` | 28 / 1036 | WP-checked primitive implementations; runtime adapter |
| `verification/early.c` | 43 / 1100 | Generated completed theorem and unreachable-suffix assertion |
| `verification/check.sh` | 13 / 590 | Replay orchestration |
| `verification/instrument.py` | 52 / 2692 | Trusted access instrumentation for finite tests |
| `verification/test.mjs` | 99 / 5183 | Finite input generator, reference semantics, execution assertions |
| `verification/annotations.json` | 18 / 3008 | Candidate contracts/invariants, not universally proved |
| `verification/lifted.c` | 1038 / 23729 | Generated full model; general proof unfinished |
| `README.md` | 18 / 2872 | Requirements and interface |
| `lz4_Block_format.md` | 244 / 10683 | Format meaning used when interpreting results |

For finite tests, also trust Clang/wasm-ld's compilation of the lift, Node's
WebAssembly implementation, and the instrumentation transformation. The
original binary is instantiated directly; no rebuild of the shipped artifact
is substituted for it. Generated `.wasm`/`.wat` files and logs can be recreated
and are not additional specifications. No Lean theorem or proof of the
original C compiler is claimed.
