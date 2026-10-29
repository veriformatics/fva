This is a **partial verification**. R1, R2, and R3 have not been proved over
the full domain in README.md, and no counterexample to them was found. The
results below must not be read as a certificate that the decoder meets all
three requirements. They establish finite execution results for the shipped
instruction stream in a reviewed Lean model, with an independent Wasmtime
replay, and auxiliary general theorems.

The artifact examined is `lz4-flex.wasm`, 7,161 bytes, SHA-256
`1f115e3a5ddee865621f406e2abf545854218cb8dc632d759e998553031aa775`.
The original artifact, README, format document, Rust sources, and build script
are unchanged. There was no network access or Rust rebuild.

1. Results for each requirement

   All names below are in namespace `LZ4Verification`. The concrete inputs,
   addresses, capacities, and expected outputs are in `Proofs/Cases.lean` and
   `verification/cases.json`. `cases` contains exactly 42 cases. Caller memory
   initially contains zero except for the supplied compressed input. These are
   individual cases, not exhaustive input classes and not all initial memories.

   R1: **Unproved in general.** In `Proofs/Results.lean`:

   ```lean
   theorem cases_R1_trace (c : Case) (hc : c ∈ cases) :
       ∃ r s, runCase c = some (r, s) ∧
         ∀ a ∈ s.trace, safeAccess c a = true
   ```

   `trace` includes every modeled load, store, bulk-copy source/destination,
   and fill destination, with the full access width. `safeAccess` requires
   each read to lie entirely inside the source or destination buffer, and each
   write entirely inside the destination buffer. It is stronger than R1 for
   these cases because it permits no accesses below 131072 either. `runCase`
   returning `some` excludes an unsupported instruction, trap, or fuel timeout.
   The native replay separately checks every caller-memory byte outside the
   destination after each call. That replay cannot detect out-of-buffer reads
   or transient writes that are restored before return.

   What remains: a universal invariant proving all decoder paths confine their
   accesses for every admissible layout, input, capacity, and initial memory.
   Safe Rust source and successful Wasm validation do not supply that proof.

   R2: **Unproved in general.** In `Proofs/Results.lean`:

   ```lean
   theorem cases_R2_content (c : Case) (hc : c ∈ cases) (d : Decoded)
       (hd : decode c.input = some d) (he : endConditions d = true)
       (hcap : d.output.length ≤ c.cap) :
       ∃ r s, runCase c = some (r, s) ∧
         correctOutput c r s d.output = true
   ```

   `decode` in `Proofs/Format.lean` is a separate executable interpretation of
   the supplied format document. It parses tokens and mandatory extensions,
   little-endian offsets, and byte-at-a-time overlapping matches. It rejects
   zero offsets and references before the beginning of this block. It consumes
   the compressed input through a final literal-only sequence.
   `endConditions` requires at least five final literals except for a single
   short literal-only block, and requires each match start to precede the
   decoded end by at least twelve bytes. Checking all match starts is equivalent
   to checking the last, since starts are recorded in increasing order.
   `correctOutput` checks the return value equals the decoded length, is at most
   capacity, and the destination prefix equals the decoded bytes.

   What remains: a completeness/refinement proof relating every valid
   independent format block to every optimized Wasm execution, including all
   loop iterations and lengths. The reference format interpretation also needs
   review against the prose; its agreement with that prose is not a theorem.

   R3: **Unproved in general.** In `Proofs/Results.lean`:

   ```lean
   theorem cases_R3_content (c : Case) (hc : c ∈ cases) (r : Nat) (s : State)
       (hr : runCase c = some (r, s)) (hn : r < 2147483648) :
       ∃ d, decode c.input = some d ∧
         correctOutput c r s d.output = true
   ```

   Wasm i32 values use unsigned representatives in the model, so the hypothesis
   on `r` is exactly signed non-negativity. This theorem imposes sequence and
   independent-offset checks, but intentionally omits `endConditions`. The case
   `end_conditions_relaxed` succeeds with input `10 41 01 00 00`, capacity 5,
   and output `41 41 41 41 41`. It violates end restrictions only and therefore
   illustrates the permission in R3; it is not a counterexample.

   What remains: a soundness/refinement proof for every nonnegative return on
   arbitrary compressed bytes, including proofs of output-position invariants
   and the validity of every accepted match offset.

   All 42 individual certificates have the exact form
   `theorem case_i_checked : checkedCase case_i = true`, for i = 0,...,41,
   in `Proofs/CaseProofs0.lean` through `Proofs/CaseProofs6.lean`.
   `checkedCase` conjoins admissibility, the expected return/output, and the
   three checks. They are combined in `Proofs/Results.lean` as:

   ```lean
   theorem cases_checked : ∀ c ∈ cases, checkedCase c = true
   theorem cases_count : cases.length = 42
   ```

   The cases cover empty blocks; literal lengths around 4, 8, 15, 16, 32, and
   255-extension boundaries; overlapping matches; hot-loop wild copies;
   32/64-byte slow-path copies; bulk copy/fill; invalid offsets; truncated
   lengths/literals/offsets; insufficient capacity; and source/destination
   buffers ending at the final byte of memory. These descriptions express
   coverage, not universal guarantees.

   General auxiliary theorems in `Proofs/Format.lean` are:

   ```lean
   theorem copyMatch_length (n offset : Nat) (out result : List Nat)
       (h : copyMatch n offset out = some result) :
       result.length = out.length + n

   theorem copyMatch_prefix (n offset : Nat) (out result : List Nat)
       (h : copyMatch n offset out = some result) :
       out.IsPrefix result

   theorem length_accumulator_no_wrap (n len : Nat)
       (hn : n ≤ 1966080) (hlen : len ≤ 255*n + 19) :
       len < 4294967296
   ```

   The first two concern the reference match copier. The last is arithmetic
   relevant to this caller-memory domain, not a proof that the artifact's
   accumulators satisfy its premises at every program point.

2. Connection to the shipped bytes

   `Proofs/Artifact.lean` embeds every byte of the artifact as natural numbers.
   `verification/check.py` compares this literal byte-for-byte with the actual
   file, verifies the stated hash/size, and uses `wasm-tools` to validate the
   module and confirm that the export is function 7 with four i32 parameters
   and an i32 result, memory is fixed at 32 pages, and imports/start functions
   are absent.

   The Lean parser in `Proofs/Wasm.lean` reads the binary header, sections,
   code-body vector, function 7's local declarations, and instruction bytes.
   It requires empty block/loop signatures, decodes signed constants and memory
   offsets, and rejects unsupported encodings. `annotate` computes matching
   block ends. In `Proofs/Extraction.lean` the exact statement is:

   ```lean
   theorem extraction_exact :
       extractedProgram.map (fun (n, code) => (n, annotate code)) =
       some (24, program)
   ```

   `program` in `Proofs/Program.lean` has 982 instructions. A checked balanced
   lookup table avoids slow linear instruction fetches during kernel reduction:

   ```lean
   theorem program_tree_exact : programTree.toList = program.toList ∧
       programTree.wellFormed = true ∧ vmProgram.size = program.size
   ```

   `CodeTree.get?_eq` in `Proofs/Wasm.lean` proves tree lookup equals indexing
   its flattened instruction list for any well-formed tree.

   The execution model implements only the integer/control/memory subset
   needed here. Calls and unsupported instructions return `none`; they are
   not modeled as successful decoder returns. The 42 checked paths execute no
   calls and no accesses to module stack/static data. Consequently the model's
   zero default below the caller region is not used on those paths. The fuel
   limit is 20,000 steps per case; a timeout fails its certificate.

   **There is no formal refinement theorem from this custom interpreter to
   the official Wasm semantics.** That is a trust boundary, even though the
   instructions come from the exact shipped bytes. Wasmtime independently runs
   the real exported function on all 42 cases, comparing its return, successful
   output, and every caller byte outside the destination. No claim depends on
   Rust-to-Wasm compiler correctness or on rebuilding equivalent source.

3. Reproduction from this directory, without network access

   ```sh
   python3 verification/check.py
   lake build
   lake env lean verification/Audit.lean
   ```

   The Python command must exit 0 and print three PASS lines for the byte
   bridge, 42-case bridge, and Wasmtime replay. The Lake command must exit 0
   with `Build completed successfully`; it checks the extraction, lookup table,
   case certificates, combined results, and auxiliary proofs. Case and
   extraction certificates use `decide +kernel`, not `native_decide`.
   The audit prints dependencies of the principal theorems. It must contain
   no `sorryAx` or native-evaluation/compiler-trust axiom. Standard foundational
   axioms, where reported, are identified by Lean in that output.
   The completed audit reported only `propext`, `Classical.choice`, and
   `Quot.sound`; `program_tree_exact` had no axiom dependencies.

   Generated data can optionally be recreated, then rechecked:

   ```sh
   lake build Proofs.Wasm
   lake env lean --run verification/Extract.lean
   python3 verification/generate_cases.py
   lake build
   python3 verification/check.py
   ```

   Generation does not establish any result; the subsequent kernel checks and
   byte/case comparisons do. Wasmtime's cache is explicitly disabled so replay
   does not require writing outside the workspace/temporary directory.

4. Review and trust

   Read the model/format/check definitions as well as the theorem statements.
   The two central interpretation assumptions are that `Proofs/Wasm.lean`
   implements the relevant Wasm semantics and that `Proofs/Format.lean`
   correctly formalizes the supplied LZ4 prose. Kernel reduction proves results
   about those definitions; it cannot establish those interpretation assumptions.
   The byte/case bridge and runtime replay additionally trust Python's file and
   subprocess operations, `hashlib`, `wasm-tools`, and Wasmtime. No external
   service or additional Python package is used.

   Lean 4.35.0's kernel and its handling of the imported built Mathlib v4.35.0
   environment are trusted. The generators need not be trusted: their emitted
   program/table is checked against binary extraction, and their emitted cases
   are compared to the native replay data. The report is an explanation, not a
   proof object. Source sizes are recorded below after successful checking.

   | Review material | Lines | UTF-8 bytes |
   | --- | ---: | ---: |
   | Requirements and supplied format | 262 | 13,085 |
   | Wasm parser, lookup, and execution model | 373 | 13,068 |
   | Reference format and auxiliary proofs | 111 | 4,503 |
   | Case initialization and requirement checks | 78 | 2,187 |
   | Embedded binary and extracted instruction/table data | 1,238 | 74,862 |
   | Concrete Lean case data | 136 | 11,994 |
   | Native replay case data | 2,424 | 26,516 |
   | Individual case certificates | 140 | 4,012 |
   | Extraction, combined results, root, and audit | 139 | 4,799 |
   | Byte/case bridge and Wasmtime replay script | 123 | 6,016 |
   | Optional generators | 127 | 5,713 |

   The embedded/extracted data and case vectors are listed separately from
   the executable definitions so their size is not mistaken for semantic
   modeling effort. The model/check definitions total 562 lines (19,758 bytes).
   The external runtime versions used were Wasmtime 50.0.0 and wasm-tools
   1.262.0. Their implementations and the Lean/Mathlib installation are
   preinstalled toolchain dependencies, not included source in this delivery.
