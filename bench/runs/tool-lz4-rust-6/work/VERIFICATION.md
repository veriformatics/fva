# Verification results

**The universal requirements R1–R3 remain unproved. No counterexample was found.**
This delivery contains Verus proofs of restricted executions of a model extracted
from the exact shipped Wasm, five general mathematical lemmas, and direct
Wasmtime checks of the original artifact. The restricted proofs and tests are
not a proof that the artifact satisfies every README requirement.

## Artifact and model connection

The artifact is the existing `lz4-flex.wasm`, unchanged: **7,161 bytes**, SHA-256
`1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775`.

`verification/generate.py --check` checks that length and hash, disassembles the
binary using `wasm-tools print`, checks its fixed 32-page memory and decoder
export, and compares its generated function-7 instruction table against
`verification/program.inc.rs`. No Rust source rebuild or assumption about the
Rust compiler is used. The table contains 878 operations, including a terminal
`Unsupported` sentinel. Zero-result Wasm blocks and loops are flattened into
instruction indices; branch targets are resolved from the original nesting.
The generator checks empty operand stacks at reachable label entries.

`verification/machine.rs` defines an integer-valued, small-step Wasm interpreter
for that table. It models locals, operand stack, modulo-2^32 arithmetic,
unsigned comparisons, shifts, little-endian loads/stores, `select`, branches,
`memory.copy` with snapshot semantics, and `memory.fill`. Memory is represented
by an initial buffer description and a byte-write log. Calls, unreachable
instructions, unsupported instructions, invalid accesses, and invalid stack
operations produce `Unsupported`, which cannot satisfy a returned-result
predicate. All proved executions return within the specified fuel bound; fuel
exhaustion is not treated as success.

The `safe` flag starts true and is conjoined with the access restriction at
every memory operation. For a nonempty access, reads must lie wholly in the
source or destination buffer; writes must lie wholly in the destination.
Consequently `safe` is stronger than R1's restriction to addresses at least
131072. Bulk operations check their entire ranges. The placeholder zero value
for other memory cannot affect these executions: their proved `safe` flag
excludes all reads of that memory. Initial destination bytes are 165 in the
concrete proofs. Memory outside the two buffers may otherwise be arbitrary.

**The extraction and interpreter are trusted models, not a formally verified
Wasm frontend or a proved implementation of the WebAssembly specification.**
Verus checks their stated theorems; it does not prove their correspondence to
the binary or to Wasm semantics. The generation check binds the table to this
binary through the reviewed generator. The separate Wasmtime harness imports
and executes the original binary, not the model or the Rust source.

## Exact proved statements

The definitions below are in `verification/machine.rs` and
`verification/format.rs`. Concrete theorem statements are in
`verification/cases.inc.rs`; all use `assert(...) by(compute)` with Verus.

For every row below, let `m = NAME_input()` and
`s = run(m, initial(m), 3000)`. The theorem named `NAME_checked` has the exact
postcondition `NAME_property()`. Each such predicate asserts:

* `init_ok(m)`: nonnegative lengths, buffers within `[131072,2097152)`,
  disjoint buffers, and byte-valued input and seed;
* `s.safe`;
* `returned(s, r)`, with the table's return value, represented modulo 2^32.

Every successful row additionally asserts exactly:

* `read_output(m,s,0,L) == E`, where `E` is that row's expected byte sequence
  and `L = E.len()`;
* `encoding(NAME_certificate()) == m.input`;
* `decoded(NAME_certificate(),seq![]) == E`;
* `grammar(NAME_certificate(),seq![])`;
* `valid_block(NAME_certificate()) == B`, with `B` from the table;
* `L <= m.cap`.

The literal input and expected output arrays are specified in the checked
Rust statements and in `verification/cases.json`; neither is an oracle obtained
from the production decoder. Every concrete row uses `src=131072`, `dst=262144`,
and initial destination byte 165.

| NAME | n | cap | r | B / intended case |
| --- | ---: | ---: | ---: | --- |
| `empty_input` | 0 | 0 | -1 | error |
| `empty_block` | 1 | 0 | 0 | true; input `00` |
| `one_literal` | 2 | 1 | 1 | true; input `10 41` |
| `slow_overlap` | 10 | 13 | 13 | true; offset 1, match length 7 |
| `hot_overlap` | 19 | 64 | 22 | true; hot loop, overlapping match |
| `hot_snapshot18` | 22 | 64 | 22 | true; hot loop, 18-byte snapshot |
| `slow_snapshot32` | 30 | 100 | 43 | true; extended lengths, 32-byte snapshot |
| `slow_snapshot64` | 44 | 110 | 71 | true; extended lengths, 64-byte snapshot |
| `extended_literals` | 18 | 16 | 16 | true; literal extension byte |
| `relaxed_end` | 5 | 5 | 5 | false; input `10 41 01 00 00` |
| `zero_offset` | 10 | 32 | -1 | error; input `10 41 00 00 50 42 43 44 45 46` |
| `offset_beyond_prefix` | 3 | 64 | -1 | error; input `00 01 00` |
| `truncated_literal` | 2 | 32 | -1 | error; input `20 41` |
| `truncated_extension` | 2 | 32 | -1 | error; input `f0 ff` |
| `truncated_offset` | 3 | 64 | -1 | error; input `10 41 01` |
| `output_too_small` | 2 | 0 | -1 | error; input `10 41` |

`grammar` checks token fields, exact extension-byte encodings, literal bytes,
16-bit little-endian offsets, positive offsets no larger than the already
produced prefix, match lengths of at least four, and a final literal-only
sequence. `decoded` implements forward, overlapping match copies.
`valid_block` additionally requires a nonempty sequence list and, when there
are matches, at least five final literals and a last match starting at least
12 decoded bytes before the end. A single literal-only sequence also represents
short and empty contents. These are reviewed definitions interpreting
`lz4_Block_format.md`, not a machine-checked translation of its prose.

There is also a restricted universal theorem in `verification/machine.rs`:

```text
zero_length_input_all_placements(src:int, dst:int, cap:int, seed:int)
requires init_ok(Init { src, dst, input:seq![], cap, seed })
ensures {
  let m = Init { src, dst, input:seq![], cap, seed };
  let s = run(m,initial(m),20);
  s.safe && returned(s,-1) && s.writes.len() == 0
}
```

Five general supporting theorems are in `verification/format.rs`. Their exact
statements, using the file's `sum` and `repeat_match` definitions, are:

1. `sum_bound(s)`: if `bytes(s)`, then
   `0 <= sum(s) <= 255*s.len()`.
2. `length_no_u32_overflow(s,base)`: if `bytes(s)`, `s.len() <= 1966080`, and
   `0 <= base <= 19`, then `0 <= base+sum(s) <= 501350419` and
   `base+sum(s) < 4294967296`.
3. `hot_copy_bounds(n,cap,ip,op,lit,offset,ml)`: assuming
   `0<=n,cap<=1966080`, `0<=ip`,
   `ip+1 <= (if n>=18 {n-18} else {0})`, `0<=op`,
   `op < (if cap>=34 {cap-34} else {0})`, `0<=lit<=14`,
   `4<=ml<=18`, and `1<=offset<=op+lit`, proves all of:
   `ip+1+16<=n`, `ip+1+lit+2<=n`, `op+16<=cap`,
   `op+lit+ml<=cap`, `0<=op+lit-offset`, `op+lit+18<=cap`,
   and `op+lit-offset+18<=cap`. All parameters are mathematical integers.
4. `repeat_match_preserves_prefix(prefix,offset,count)`: assuming
   `1<=offset<=prefix.len()`, for natural `count`, proves
   `repeat_match(prefix,offset,count).len() == prefix.len()+count` and,
   for every `0<=i<prefix.len()`,
   `repeat_match(prefix,offset,count)[i] == prefix[i]`.
5. `snapshot_match_byte(prefix,offset,count,i)`: assuming
   `1<=offset<=prefix.len()`, natural `count<=offset`, and `0<=i<count`,
   proves `repeat_match(prefix,offset,count)[prefix.len()+i]
   == prefix[prefix.len()-offset+i]`.

The mathematical lemmas address length overflow and optimized-copy reasoning;
they do not establish invariants for every reachable artifact state.

## Result for each README requirement

**R1 — partially established, universal requirement unproved.** Every listed
concrete model execution satisfies the access restriction, including malformed
inputs and unsuccessful calls. The zero-length-input theorem covers every
admissible buffer placement and capacity for `n=0`. Direct artifact execution
also checks write confinement for all 16 concrete cases. Missing: a universal
invariant establishing access safety of the decoder's loops for arbitrary
nonempty inputs, capacities, placements, and destination contents. Finite
execution checks cannot fill that gap. There is no demonstrated R1 violation.

**R2 — eight valid independent blocks checked, universal requirement unproved.**
The eight successful rows with `B=true` each have a checked valid-format
certificate, checked exact decoded bytes and return length, and sufficient
capacity. They cover slow and hot loops, overlapping and snapshot matches,
empty output, and extended lengths. Missing: a completeness/refinement proof
for arbitrary valid blocks, including arbitrary sequence counts and extension
chains. There is no demonstrated R2 violation.

**R3 — nine successful executions checked, universal requirement unproved.**
All nine successful rows have checked sequence-splitting certificates, valid
independent offsets, matching decoded content and returned length, and
`r<=cap`. `relaxed_end` demonstrates permitted acceptance when only the end
conditions fail: it decodes to five `41` bytes. It is **not** a counterexample
to R3. Missing: an invariant extracting a grammar/decoding certificate from
every possible successful artifact execution, including its optimized paths.
There is no demonstrated R3 violation.

## Reproduction

From this directory run:

```sh
bash verification/check.sh
```

The script runs exactly:

```sh
python3 verification/generate.py --check
python3 verification/generate_cases.py --check
wasm-tools validate lz4-flex.wasm
verus --version
verus --no-cheating verification/machine.rs
wasmtime run -C cache=n --preload decoder=lz4-flex.wasm --invoke check verification/runtime.wat
```

Success means both generation checks print `PASS`, validation exits zero,
Verus reports `37 verified, 0 errors`, and Wasmtime prints `16` and exits zero.
The Wasmtime experimental-`--invoke` warning is harmless. Verification may take
several minutes. No network, Lake build, Rust rebuild, or Lean proof is used.
Verus was run with release `0.2026.10.18.7d82994`; `--no-cheating` excludes
`assume`, `admit`, `external_body`, and `assume_specification` in these proofs.

The Wasmtime harness initializes caller memory, imports the original decoder
and memory, checks all returns and successful decoded bytes, and checks every
byte in `[131072,2097152)` outside the declared destination against its initial
value after each call. A failed check traps. This runtime check does not observe
reads and is explicitly a finite test, not a universal proof.

## Review and trust inventory

Sizes are source lines / bytes; generated files are included for reproduction.

| File | Lines | Bytes | Role |
| --- | ---: | ---: | --- |
| `verification/machine.rs` | 222 | 8534 | Reviewed interpreter, access restriction, initialization, universal restricted theorem |
| `verification/format.rs` | 171 | 6364 | Reviewed format/decoding definitions and general proofs |
| `verification/generate.py` | 139 | 6112 | Trusted binary binding and Wasm control-flow/opcode translation |
| `verification/cases.py` | 53 | 2298 | Reviewed inputs and certificates |
| `verification/generate_cases.py` | 79 | 4363 | Generates theorem predicates, vectors, direct runtime harness |
| `verification/check.sh` | 10 | 406 | Reproduction driver |
| `verification/program.inc.rs` | 3517 | 180030 | Generated opcode table; compared to extraction |
| `verification/cases.inc.rs` | 298 | 13185 | Generated exact theorem statements and compute proofs |
| `verification/cases.json` | 799 | 10493 | Generated explicit input/output vectors |
| `verification/runtime.wat` | 664 | 38876 | Generated Wasmtime assertions |

The handwritten verification sources total **674 lines / 28,077 bytes**.
The full verification directory's ten source/data files total
**5,952 lines / 270,661 bytes**. Generation checks allow reviewing the small
generators instead of independently trusting manually maintained generated
files. Nevertheless, neither generator is itself formally verified.

The requirements and format being interpreted are `README.md` (18 lines /
2,402 bytes), `CHECK.md` (8 / 784), and `lz4_Block_format.md` (244 / 10,683).
The artifact is 7,161 bytes. The vendored Rust and build script are explanatory
context; these results do not depend on source/binary equivalence.

External trusted infrastructure includes Verus and its compute evaluator,
Rust frontend, supplied vstd specifications, Z3, Python 3.14.8 with hashlib,
`wasm-tools` 1.262.0 for binary validation/disassembly, and Wasmtime 50.0.0 for
the separate runtime evidence. Installed key binary sizes: `rust_verify`
25,483,272 bytes; `vstd.vir` 30,838,617; `libvstd.rlib` 9,864,436; Z3
34,954,456; `wasm-tools` 20,431,992; Wasmtime 67,968,088. These sizes do not
include their transitive libraries, operating system, or hardware. No new
axioms or unchecked proof stubs were introduced. Semantic fidelity of the
reviewed definitions and extraction remains a trust obligation; full universal
verification remains outstanding.
