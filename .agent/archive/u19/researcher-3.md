# researcher-3 — Wasm program proofs, access footprints, LZ4 prior art

| id | question | answer | numbers | source (URL + verbatim excerpt) | applicability |
|---|---|---|---|---|---|
| C1 | Mechanized Wasm semantics with program-level proofs (WasmCert-Coq, WasmCert-Isabelle, Iris-Wasm, Wasm-Logic / separation logic for Wasm, Talos): any all-input proof about a compiled C/Rust function with loops; method + size | **Yes: Talos has an optimized Rust `num-integer` gcd loop with all-input total correctness over its generated Wasm AST.** Method = instruction WP + loop invariant / Löb induction for partial correctness, separate finite-trace well-founded termination, then composition. WasmCert supplies language/type-safety/interpreter foundations, not itself this production-function proof. Wasm Logic verifies a directly implemented Wasm B-tree; Iris-Wasm verifies a directly implemented higher-order stack. No compiled-C decoder example confirmed in these projects. See C1 details. | Talos Cargo profile: `opt-level = 3`; inspected pinned Spec file = 950 lines (local wc, includes legacy + small-step proofs, excludes shared library); Iris paper: stack binary 637 bytes / ≈200 Coq program lines / ≈3800 Coq proof lines; Wasm Logic mechanization ≈10,400 Isabelle lines (framework, not B-tree proof alone). | [Talos pinned Cargo.toml](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/rust/Cargo.toml#L31-L35): `opt-level = 3`; [Talos theorem](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Spec.lean#L885-L905): `∀ input : Input,` / `∃ output : Output,` / `Runs "gcd_u64" (args input) (result output) ∧` / `output.toNat = Nat.gcd input.left.toNat input.right.toNat`; [Iris paper p.18](https://iris-project.org/pdfs/2023-pldi-iris-wasm.pdf): `binary size of 637 bytes` / `around 200 lines code in Coq` / `around 3800 lines of code in Coq`; [Wasm Logic p.2](https://www.cl.cam.ac.uk/~nk480/wasm-pl.pdf): `Our mechanisation totals ~10,400 lines of non-comment, non-whitespace Isabelle code, not counting code inherited from the existing mechanisation.` | Good precedent for reusable WP, explicit generated-loop invariants, and separate termination arguments; **not** evidence that an optimized decoder with memory + overlap is already solved. Talos AST fidelity uses generated WAT macros + `#eval` check, not FVA's kernel-checked byte decoder. No upstream proof builds rerun. |
| C2 | How binary/Wasm-level proofs state a memory-access footprint ("reads only within A, writes only within B" at every step, not just the final store): trace predicates, separation-logic frames, instrumentation; examples + exact formulations | Best exact binary precedent = s2n-bignum eventful ISA semantics: every load/store emits address + byte length; `memaccess_inbounds` universally checks the trace against separate readable/writable range lists. Wasm separation-logic precedent = Iris load/store rules require ownership of every byte touched and return/update it; use stepwise ownership/simulation, not final heap equality alone. See C2 exact code + FVA translation. | Access width is part of each event; no empirical effort number needed. The s2n implementation supports architecture-width-parametric modular containment. | [s2n SOUNDNESS §A4](https://github.com/awslabs/s2n-bignum/blob/main/SOUNDNESS.md#A4-memory-safety): `The frame condition constrains only what is written (and only by comparing initial and final states)` / `Out-of-bounds reads are not excluded` / `Transient writes (writing then restoring a value) are not excluded either.`; [pinned safety.ml:142–157](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/common/safety.ml#L142-L157): `ALL (\(e:(A)address_uarch_event). match e with` / `EventLoad (adr,sz)` → `readable_ranges` / `EventStore (adr,sz)` → `writable_ranges`; [Iris rules:1826–1837,1996–2006](https://github.com/logsem/iriswasm/blob/e37f8387a1171d104d78a2f77f9e637e090cf3d4/theories/iris/rules/iris_rules_resources.v#L1826-L1837): `N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ] (bits v)` / store: `length bs = length_t t` (full formulas below). | R1 should quantify over **every finite reachable prefix**, including error paths and divergent prefixes; each access range intersected with caller-address band must lie in allowed read/write sets. Add observation-only instrumentation + erasure theorem, or define accesses directly from each small step. Final-store frame and input/output dependence are both insufficient. This formulation is a proposal/inference, not an already-proved FVA theorem. |
| C3 | Formally verified LZ4 (or LZ77-family) decompressors in any tool (Coq, Isabelle, F*, Dafny, Verus, SPARK, Frama-C, Lean, Why3): what was proved (memory safety, functional correctness vs a format spec), at source or binary level, effort | **LZ4-specific complete proof: none found in searched primary literature/repos.** Important negative lead: Theorem/Anthropic publishes LZ4 RISC-V fuzz-target **statements**, but inspected `round_trip_fuzzer` status is open, not a proof. Strong LZ77-family functional precedent = Coq DEFLATE (format relation + compressor/decompressor correctness); Lean-zip = pure-Lean round trip. Anthropic reports binary-level LZO round-trip proof, but this survey did not replay it. Details + search ledger C3. | LZ4 published target pins commit `0774d05537f9762f838f7ab541b7765f1a729cb5`, not spike v1.10.0; LZ4 target status explicitly `open`. No LZ4 proof-effort number confirmed. | [Theorem pinned LZ4 README](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/projects/lz4/round_trip_fuzzer/README.md): `Linked against lz4 at commit 0774d055.` / `LZ4_compress_default into a bound-sized buffer must succeed and LZ4_decompress_safe must regenerate exactly the input`; [pinned statements index](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/index/statements.tsv): `lz4/round_trip_fuzzer/plain_halts` ... `open`; [Coq paper](https://arxiv.org/pdf/1609.01220): `a reference implementation of both a compression and decompression algorithm which have been formally verified against this specification and tested against the ZLib`; [Anthropic appendix p.6](https://www-cdn.anthropic.com/files/4zrzovbb/website/6867eadf760258fa8b42a504600cd3c036d16358.pdf): `Claude had to prove that LZO’s compressor and decompressor round-trip correctly`. | No pre-existing proof of the exact LZ4 artifact/requirements to port was confirmed. Round-trip only covers encoder-produced blocks, not every format-valid input (R2), arbitrary-byte footprint (R1), or accepted-input characterization (R3). Source/model correctness ≠ compiled-artifact correctness. |
| C4 | Verified decompressors more broadly (DEFLATE/zlib, Brotli, zstd, e.g. in Coq/HOL/F*/Rocq, EverCrypt-style): loop invariants used for back-reference copies (overlapping match copy), proof effort | Strongest established functional precedent: Senjak–Hofmann Coq DEFLATE, relational format spec + extracted verified resolver, explicitly supports overlap (length > distance). Recent source-linked but narrower precedent: Certora CLean proves zlib `inflate_table` memory safety + termination, not whole decompression / functional correctness / compiled code. Lean-zip proves pure-Lean round trips, with trusted C primitive replacements. mbrotli/mzstd prove selected RFC arithmetic/tables through Aeneas; whole-decoder refinement remains future work. See C4 details. | Certora reports 266 C lines, 7 loops, ≈20,000 Lean lines, ≈500 per-statement proofs, 32-clause main invariant, ≈two weeks; lean-zip README reports >1,100 theorems / ≈32k proof lines. These are source-reported, not independently measured. | [Coq DEFLATE paper §4](https://arxiv.org/pdf/1609.01220): `This intuitive algorithm works when l > d, and results in a repetition of already written bytes`; §4.1: `we have a fully verified implementation in EfficientDecompress.v`; [CLean](https://www.certora.com/blog/formally-verifying-zlib-memory-safety-with-lean): `Our scope included 266 lines of C, 7 loops, and 7 return sites.` / `around 20,000 lines of Lean, roughly 500 per-statement proofs, one main-loop invariant with 32 clauses and a termination measure.` / `took about two weeks` / `not (yet) functional correctness` / `not about compiled machine code`; [lean-zip](https://github.com/kim-em/lean-zip/blob/master/README.md): `more than 1,100 theorems across ~32k lines of proof` / `the proofs are about the reference bodies, and the C is trusted to match them`; [mbrotli/mzstd](https://m-compressors.github.io/2026/formal-verification-mbrotli-mzstd/): `They are not verified codecs yet` / `A refinement proof that the baseline path of each Rust decoder computes the reference decoder’s output for any chunking of the input.` | Use an explicit evolving-output backreference relation; overlap is forward recurrence, not snapshot memcpy. Functional-model correctness is transferable only after a Wasm-to-model simulation. Effort numbers are context, not a forecast for optimized LZ4 binary proof. |
| C5 | LZ4 reference decoder specifics relevant to a proof: `LZ4_decompress_generic` fast/safe loops (shortcut path, `LZ4_wildCopy`, offset < 8 handling, end-of-block margins MFLIMIT / LASTLITERALS), as documented upstream | Safe full-block/no-dictionary specialization; architecture-gated 32-byte fast loop defaults off for wasm32 (inference from macro guard + build flags, not binary inspection). Remaining main loop has speculative literal/match stripes, checked long lengths, wild copies, small-offset table path, exact-input-consumption terminal literals, negative error exit. See C5 details. | Upstream constants: MINMATCH 4; WILDCOPYLENGTH 8; LASTLITERALS 5; MFLIMIT 12; FASTLOOP_SAFE_DISTANCE 64; shortcut stripes 16 / 18 bytes. | [v1.10.0 lib/lz4.c](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L241-L248): `#define MINMATCH 4`, `#define WILDCOPYLENGTH 8`, `#define LASTLITERALS   5`, `#define MFLIMIT       12`, `#define FASTLOOP_SAFE_DISTANCE 64`; [macro guard](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L478-L491): `#  else` / `#    define LZ4_FAST_DEC_LOOP 0`; [safe shortcut](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2219-L2257): `copy 16 bytes on behalf of the literals` / `If the match length is 4..18, copy 18 bytes`; [instantiation](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2451-L2455): `decode_full_block, noDict,` / `(BYTE*)dest, NULL, 0` (all excerpts verbatim; detailed anchors below). | Prove the actual wasm specialization, not generic dictionary/partial/architecture-fast code. R1 permits speculative access throughout capacity, not just decoded prefix; preserve prefix correctness while treating overcopied tail separately. Memory-access widths, not merely corrected op/cpy, decide R1. |


## C1 — Wasm program-proof evidence

| project | inspected primary evidence + verbatim excerpt | confirmed scope / gap |
|---|---|---|
| WasmCert-Coq | [README](https://github.com/WasmCert/WasmCert-Coq/blob/master/README.md): `Soundness results for WasmRef-Coq (interpreter) with respect to WasmCert-Coq.` / `Type safety results for Wasm typing system.` / `Soundness and completeness results for the type checker with respect to the typing system.` / `This repository contains a mechanised Wasm program logic using the Iris framework`. | Language metatheory + program-logic foundation. Inspected README points to Iris for individual program verification; it does not exhibit a compiled-C decoder proof. Its binary parser is explicitly experimental: `a parser for the binary format which is currently unverified`. |
| WasmCert-Isabelle | [README](https://github.com/WasmCert/WasmCert-Isabelle/blob/master/README.md): `The type soundness statement and proof can be found in WebAssembly/Wasm_Soundness.thy.` | Type soundness ≠ functional correctness of arbitrary compiled functions or buffer-local memory safety. No compiled-C/Rust loop example confirmed from inspected README + paper search. |
| Wasm Logic | [paper abstract + p.2](https://www.cl.cam.ac.uk/~nk480/wasm-pl.pdf): `Using Wasm Logic, we specify and verify a simple WebAssembly B-tree library` / `We mechanise Wasm Logic and its soundness proof in full in Isabelle/HOL` / `Our mechanisation totals ~10,400 lines of non-comment, non-whitespace Isabelle code, not counting code inherited from the existing mechanisation.` | Separation logic + structured-control Hoare rules; big-step semantics proven equivalent to transitive closure of small-step semantics. B-tree is implemented directly in Wasm, not identified as C/Rust output. Caution: inspected paper establishes mechanization of the logic/soundness; this survey did not locate/replay a mechanized B-tree artifact, so do not equate that code-size figure with a mechanically checked B-tree proof. |
| Iris-Wasm | [paper p.18](https://iris-project.org/pdfs/2023-pldi-iris-wasm.pdf): `with an extra requirement that the frame resource holds for every step of reduction`; `The stack module, with a binary size of 637 bytes, is defined in around 200 lines code in Coq` / `around 3800 lines of code in Coq, where 2100 lines are used to verify each of the module function specifications`. [artifact README](https://github.com/logsem/iriswasm/blob/e37f8387a1171d104d78a2f77f9e637e090cf3d4/README.md): `each of its module function implemented and verified in an individual file under theories/iris/examples/stack/function/`. | All-input abstract stack specifications, higher-order map loop, adversarial clients, modular instantiation. Programs are explicit Wasm ASTs in Coq; no compiled-C/Rust claim confirmed. Reported proof size includes instantiation/auxiliaries, not just one loop. |
| Talos | [pinned Rust source](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/rust/num_integer_opt3/src/lib.rs#L1-L9): `use num_integer_dep::Integer;` / `Integer::gcd(&a, &b)`; [Cargo profile](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/rust/Cargo.toml#L31-L35): `opt-level = 3` / `[profile.release.package.num_integer_opt3]` / `opt-level = 3`; [Program.lean:15–25](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Program.lean#L15-L25): `watFunctionBody% "../rust/build/num_integer_opt3/program.wat" 0` / `#eval Wasm.checkWatFidelity`. | Positive compiled/optimized Rust loop precedent. Proof concerns the generated AST; WAT decoding/fidelity is a macro/runtime check, unlike FVA's kernel-checked bytes-to-module theorem. [README license](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/README.md#license): `GNU Affero General Public License v3.0`. Reference method, not copyable Apache-compatible implementation advice. |

Talos exact all-input contract, [Spec.lean:889–901](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Spec.lean#L889-L901):

```lean
def GcdU64Spec : Prop :=
  ∀ input : Input,
    ∃ output : Output,
      Runs "gcd_u64" (args input) (result output) ∧
      output.toNat = Nat.gcd input.left.toNat input.right.toNat
```

Method anchors:
- [Spec.lean:155–177](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Spec.lean#L155-L177): `Partial-correctness loop invariant for the generated subtract-and-halve kernel.` / `Löb induction is sufficient` / `iloeb as IH generalizing %x %y %hxne %hyne %hxodd %hyodd %hxyne %hgcd`; state tracks nonzero odd operands, unequal until exit, gcd preserved, and recombination with the shared shift.
- [Spec.lean:688–699](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Spec.lean#L688-L699): `The measure is the sum of the two positive odd operands` / `induction hmeasure : x.toNat + y.toNat using Nat.strong_induction_on`.
- [Spec.lean:778–784](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Spec.lean#L778-L784): `TerminatesWith.of_termination_and_partial` combines the separate termination and partial-correctness theorems.
- New reusable total loop rule also exists: [SmallStepTotalLoop.lean:27–53](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/codelib/CodeLib/SepLogic/SmallStepTotalLoop.lean#L27-L53): `theorem twp_loop_wf_family` / `⌜measure j < measure i⌝ -∗ I j -∗` recursive WP. This survey read the rule; it did not establish which examples already use it.

Local textual measurement, not upstream effort estimate:
- Command: `wc -l /tmp/researcher-3/talos/programs/lean/Project/NumIntegerOpt3/{Program,Spec}.lean`.
- Verbatim output: `27 .../Program.lean`, `950 .../Spec.lean`, `977 total`. Includes blank/comment lines + retained legacy proofs; excludes shared math/WP/semantics. No meaningful total project-specific effort/time number established.
- Textual hole scan positive control: `rg -c '^theorem ' .../Spec.lean` → `21`, rc 0. `rg -n '\b(sorry|admit|axiom)\b' .../Spec.lean` → no matches, rc 1. Scope = this one file only; not a kernel replay or dependency axiom audit.

## C2 — Access footprints are execution properties

### Exact binary formulation

[s2n-bignum `common/safety.ml:142–157`](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/common/safety.ml#L142-L157), verbatim:

```ocaml
let memaccess_inbounds_def = new_definition `
  memaccess_inbounds (e2:((A)address_uarch_event)list)
                  (readable_ranges:(A word#num)list)
                  (writable_ranges:(A word#num)list) <=>
    ALL (\(e:(A)address_uarch_event). match e with
      | EventLoad (adr,sz) ->
        EX (\range. contained_modulo
            (2 EXP dimindex(:A))
            (val adr, sz) (val (FST range), SND range))
           readable_ranges
      | EventStore (adr,sz) ->
        EX (\range. contained_modulo
            (2 EXP dimindex(:A))
            (val adr, sz) (val (FST range), SND range))
           writable_ranges
      | _ -> true) e2`;;
```

Concrete application, [ARM SHA3 safety theorem:500–527](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/arm/proofs/sha3_keccak_f1600.ml#L500-L527):

```ocaml
exists e2.
    read events s = APPEND e2 e /\
    e2 =
    f_events rc a pc (word_sub stackpointer (word 128))
    returnaddress /\
    memaccess_inbounds e2
    [a,200; rc,192;
     word_sub stackpointer (word 128),128]
    [a,200; word_sub stackpointer (word 128),128]
```

Distinct readable/writable sets → round constants are readable but not writable; the data buffer and stack are both. These literal sizes belong to that source theorem, not an FVA recommendation.

Instrumentation completeness is part of the contract, not optional logging. [`common/safety.ml:24–33`](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/common/safety.ml#L24-L33): `One instruction can raise multiple events` / `PUSH and POP ... must still explicitly raise EventLoad and EventStore because otherwise memory safety check will miss out-of-bounds stack access.` [`MEMACCESS_INBOUNDS_APPEND`:183–186](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/common/safety.ml#L183-L186): concatenated trace in bounds iff both subtraces are; supports compositional loop/callee summaries.

### Wasm ownership alternative, with an important limit

[Iris-Wasm load rule:1826–1837](https://github.com/logsem/iriswasm/blob/e37f8387a1171d104d78a2f77f9e637e090cf3d4/theories/iris/rules/iris_rules_resources.v#L1826-L1837) demands byte ownership at effective address and preserves it:

```coq
N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ] (bits v)
```

[Store rule:1996–2006](https://github.com/logsem/iriswasm/blob/e37f8387a1171d104d78a2f77f9e637e090cf3d4/theories/iris/rules/iris_rules_resources.v#L1996-L2006) demands `length bs = length_t t`, ownership of `bs` at effective address, and returns ownership of `(bits v)` there. [Paper p.18](https://iris-project.org/pdfs/2023-pldi-iris-wasm.pdf): `the frame resource holds for every step of reduction`.

Inference: prove that every instruction rule consumes only allowed owned bytes, then transport that resource invariant to an access theorem. A final-state separating conjunction by itself is not such a theorem, and allowing load/store trap rules without a no-trap condition would weaken it. The inspected Iris artifact includes explicit `wp_load_failure` / `wp_store_failure` rules, so the selected WP/postcondition must distinguish admitted traps from safe execution.

### FVA R1 formulation (proposal, not an existing result)

Let `C` be the caller-address band, `S` the source range, `D` the destination-capacity range. For every finite execution prefix from a legal call, and every load/store event with byte range `E`:

```text
load  → E ∩ C ⊆ S ∪ D
store → E ∩ C ⊆ D
```

Quantify prefixes rather than only successful terminal executions: arbitrary source bytes can take error branches, and a safety claim must not become vacuous if a run fails to terminate. Use machine-address arithmetic + actual access widths; prove each event corresponds to the original small step (erasure/projection if instrumentation is added). Include helper calls, fixed globals/table reads, and stack accesses; the caller-band intersection exempts only the addresses the requirement exempts. This proposal follows the event/containment method above; no code or theorem was added to FVA.

Why not weaker substitutes? [SOUNDNESS §A4](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/SOUNDNESS.md#A4-memory-safety): `reads and writes always succeed` in its flat memory model; `The frame condition constrains only what is written (and only by comparing initial and final states)`; therefore `Out-of-bounds reads` and `Transient writes (writing then restoring a value)` are not excluded. Same logical gap applies to a flat Wasm memory model when buffers occupy subregions of an otherwise valid memory.

## C3 — LZ4-specific result and search ledger

### Theorem's published LZ4 material is an open problem set

Pinned source: [project README](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/projects/lz4/README.md#L47), verbatim: `Library: lz4/lz4 at 0774d05537f9762f838f7ab541b7765f1a729cb5`.

[round-trip target README](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/projects/lz4/round_trip_fuzzer/README.md):

```text
plain_halts ... on every input on which the plain build is never refused memory
for exceeding 16 GiB (a premise), it exits with status 0 or 2 ... open
```

[Statements.v](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/projects/lz4/round_trip_fuzzer/Statements.v#L49-L53), verbatim:

```coq
Definition plain_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain.
```

A proposition definition is not its proof. Same file says: `Whether each statement is open, proved or known false is recorded in the harness README, not here` and a proof must end in `Theorem plain_halts_holds : Statements.plain_halts.`

Primary-index measurement: fetch pinned [`index/statements.tsv`](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/index/statements.tsv). Header positive control = `id kind builds reading exits status detail revision fingerprint proof` (tab-separated). Count rows whose first field begins `lz4/`, group field `status`: verbatim output `LZ4 rows=130 open=130 other=0`. Exact sampled source row:

```text
lz4/round_trip_fuzzer/plain_halts	halts	plain	budget	0,2	open	-	1	1b1ff8259d91e1ee1345e3783743b0d6863b69aa87f736f56599625cf9542031	-
```

Inference: no currently indexed published LZ4 theorem in this pinned release. Not a claim about unpublished attempts, other versions, or all future work. The repository-wide GitHub recursive-tree response was truncated; it was used only to discover paths. Status conclusion uses the complete directly fetched statement index + directly fetched LZ4 target pages, not absence from the truncated tree.

### Search coverage / non-results

`none found` means no complete LZ4 decoder proof located, not nonexistence. Searches covered WebSearch-indexed GitHub, arXiv, academic/publisher sites, tool-project docs, and direct inspection of WasmCert, Iris-Wasm, Talos, Theorem's LZ4 index, the Coq DEFLATE paper, Lean-zip, and CLean. Query variants included:

```text
formally verified LZ4 decompressor Coq Isabelle Dafny Frama-C
LZ4 formal verification verified decompressor SPARK Why3
"LZ4" "formal verification"
"LZ4" "Coq" verified
"LZ4" "Verus"
"LZ4" "verified" "Lean"
"LZ4" "Frama-C" verification
"LZ4" "Dafny" OR "Isabelle" OR "F*" verification
"LZ4" "verified" "HOL"
"LZ4_decompress_safe" "proof" "Lean"
"LZ4" "Rocq" proof
"LZ4" "oss-verify"
"LZ4" "theorem-labs"
verified LZ77 decompressor Dafny Coq Isabelle backreferences
LZ77 LZSS decompressor SPARK Dafny verified correctness
verified decompressor Fstar LowStar EverParse compression LZ77
```

Later LZ4 queries returned the same open Theorem statements, general package lists, incidental LZ4 use in proof-file compression, or hardware-service descriptions without an inspectable decoder theorem. No relevant Frama-C / SPARK / Why3 / Dafny / Verus / F* LZ4 artifact was confirmed. A dead Coq-source lead is explicit: paper's `https://github.com/dausuu/deflate` failed `git ls-remote` with rc 128 (`could not read Username for 'https://github.com'`); this survey relies on the paper, not an inspected current proof repository there.

Nearby binary evidence, not LZ4 evidence: [Anthropic appendix p.6](https://www-cdn.anthropic.com/files/4zrzovbb/website/6867eadf760258fa8b42a504600cd3c036d16358.pdf): `Claude had to prove that LZO’s compressor and decompressor round-trip correctly` / `the proof steps through those branches at their exact addresses and shows that they are never taken.` The [main article](https://www.anthropic.com/research/formal-verification) also reports Linux-kernel zlib correctness on x86; that proof artifact was not located/replayed here. Treat these as source-reported nearby feasibility evidence, not verified proof transfers to this Wasm artifact.

## C4 — Backreference proof structure and effort

### Coq DEFLATE: declarative relation + verified functional implementation

[Senjak–Hofmann paper §1.2](https://arxiv.org/pdf/1609.01220): `a rigorous formal specification of Deflate and a reference implementation of both a compression and decompression algorithm which have been formally verified against this specification and tested against the ZLib`.

[§4](https://arxiv.org/pdf/1609.01220), verbatim imperative illustration:

```java
while (l > 0) {
  output[index] = output[index-d];
  index = index + 1; l = l - 1;
}
```

Same section: `This intuitive algorithm works when l > d, and results in a repetition of already written bytes` / `The resolution (decompression) of such backreferences in an imperative context is trivial, but uses lots of invariants that make it hard to prove correct.` They choose a purely functional resolver, not a proof of that Java loop. [§4.1](https://arxiv.org/pdf/1609.01220): exponential-list history + front/back lists bounded by the format's history distance; `we have a fully verified implementation in EfficientDecompress.v`. The faster alternatives are explicitly not yet verified: `Both perform well, and we are currently working on verifying them.` Thus do not infer that the paper proves an optimized mutable wild-copy loop.

[§5](https://arxiv.org/pdf/1609.01220): `We decided that a relational specification is clearer and easier to use` / `The final relation is called DeflateEncodes.` Strong decidability constructs a decoder and strong uniqueness gives unambiguous parsing. This supports a proof-side functional model with a small relational format spec; it does not establish correspondence with unrelated shipped code. No reliable author-hours or proof-line count was found in the inspected paper; source-level Coq extraction is the boundary, not a verified C/Wasm compilation chain.

### Lean-zip: exact overlap invariant and optimized/reference bridge

Pinned [LZ77.lean:26–38](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/LZ77.lean#L26-L38) models a valid reference as a periodic extension of the pre-copy history:

```lean
let start := acc.length - dist
let copied := List.ofFn fun (i : Fin len) =>
  acc[start + (i.val % dist)]!
resolveLZ77 rest (acc ++ copied)
```

The same definition rejects `dist == 0 || dist > acc.length`; FVA's LZ4 R3 extension for zero offset therefore needs a separate case, not direct reuse of this spec.

[InflateFastCorrect.lean:169–176](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L169-L176):

> `copyWithinAtGo writes each slot destOff + k (k < len) as a[destOff - distance + k % distance], reading only the fixed window [destOff - distance, destOff) ... and leaves positions outside [destOff, destOff + len) untouched.`

Mechanized invariant decomposition:
- Size unchanged: `copyWithinAtGo_size`.
- Before current cursor unchanged: [`copyWithinAtGo_getElem!_lt`:298–301](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L298-L301), `(hi : i < destOff + k)` → result at `i` equals input at `i`.
- Written segment periodic: [`copyWithinAtGo_getElem!_written`:323–327](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L323-L327), assumptions `0 < distance`, `distance ≤ destOff`, `destOff + len ≤ a.size`; result byte = `a[destOff - distance + ((i - destOff) % distance)]!`.
- Beyond copy end unchanged: [`copyWithinAtGo_getElem!_ge`:345–347](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L345-L347).
- Termination: each recursive proof uses `termination_by len - k`.
- Optimized cursor array equals reference append: [`copyWithinAt_extract_eq_copyLoop`:545–550](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L545-L550), verbatim signature:

```lean
theorem copyWithinAt_extract_eq_copyLoop (a : ByteArray) (outPos distance len : Nat)
    (hd : 0 < distance) (hdle : distance ≤ outPos) (hlen : outPos + len ≤ a.size) :
    (a.copyWithinAt outPos distance len).extract 0 (outPos + len)
      = Inflate.copyLoop (a.extract 0 outPos) ((a.extract 0 outPos).size - distance) distance 0 len hd
          (by rw [ByteArray.size_extract]; omega)
```

Inference for FVA: prove forward overlapping copy agrees with the same periodic-history characterization, then each fixed-width stripe/small-offset case can refine it. Maintain exact decoded prefix separately from scratch/overcopied tail. The periodic model is a *semantic normal form*, not permission to replace LZ4's runtime code or trust a model without simulation.

Boundary: [README](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/README.md): `four small stopgap primitives` / `the proofs are about the reference bodies, and the C is trusted to match them`. This is not a proof of every native memory access. Its headline `decompress(compress(data)) = data` also does not by itself prove accepted-input characterization for arbitrary compressed bytes.

### Additional scope / effort comparisons

| development | source-reported result + verbatim excerpt | relevance / limit |
|---|---|---|
| CLean zlib `inflate_table` | [Certora](https://www.certora.com/blog/formally-verifying-zlib-memory-safety-with-lean): `266 lines of C, 7 loops, and 7 return sites` / `around 20,000 lines of Lean, roughly 500 per-statement proofs, one main-loop invariant with 32 clauses and a termination measure` / `about two weeks`. Pure combinatorial model: `about 1,600 lines of it, and then showing the loop maintains the correspondence`. | Production C → mechanically emitted Clight AST → Lean semantics + separation logic. Memory safety + termination, not backreference copy / whole decompressor. Explicitly: `not (yet) functional correctness` and `our Lean development does not connect to` CompCert's compiler-correctness theorem. Source-reported effort, not independently audited. |
| Lean-zip | [README](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/README.md): `more than 1,100 theorems across ~32k lines of proof`. | Entire pure-Lean codec round trip + refinement of fast paths; no verified link from this code to the lz4 C binary. No trustworthy elapsed author-effort number established. |
| mbrotli / mzstd | [project post](https://m-compressors.github.io/2026/formal-verification-mbrotli-mzstd/): `They are not verified codecs yet` / `A refinement proof that the baseline path of each Rust decoder computes the reference decoder’s output for any chunking of the input` remains ahead. Current scope includes distance/length codes, headers, tables, repeat-offset arithmetic. | Charon/Aeneas source-to-model linkage, partial component proofs. Stateful full decoder + backreference execution not yet established. `SIMD kernels. Aeneas cannot translate them` limits the intended final theorem. |
| HOL4/CakeML Deflate-like thesis | [Carlsson–Rönning abstract](https://odr.chalmers.se/bitstreams/6308a5d9-23e0-4b38-bb2c-7f8f28bc9803/download): `Due to time constraints however, our implementation reached an executable implementation of a Deflate-like algorithm`; introduction: `The compression and decompression algorithms are defined in HOL4 and then compiled using the CakeML compiler.` | Alternative trusted compilation route for a newly written functional codec; not a verified implementation of full RFC DEFLATE nor a proof about unchanged deployed LZ4. Included to prevent overstating the thesis title as full format compliance. |

## C5 — LZ4 specialization and proof obligations

All upstream code below = [lz4 v1.10.0 `lib/lz4.c`](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c); format = [same tag `doc/lz4_Block_format.md`](https://github.com/lz4/lz4/blob/v1.10.0/doc/lz4_Block_format.md). Local snapshots: `/tmp/researcher-3/lz4/lz4.c`, `/tmp/researcher-3/lz4/format.md`. These are verbatim raw sources fetched with `webtext`, not executable downloads.

### What survives compilation

- [Instantiation:2451–2455](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2451-L2455): `decode_full_block, noDict, (BYTE*)dest, NULL, 0`. So `partialDecoding` is false, `lowPrefix=dst`, no external dictionary, and dictionary size is zero. Inference: generic dictionary/partial branches are compile-time-dead after inlining; prove the actual compiled instruction path, not all generic cases.
- [Macro:478–491](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L478-L491) enables `LZ4_FAST_DEC_LOOP` only for x86 / selected aarch64 and otherwise defines it zero. `/home/eturkes/Projects/fva/bench/tasks/lz4-c/build.sh:4–6` records a wasm32 target; verbatim flags: `-mcpu=generic -mno-simd128 -mno-relaxed-simd`, `-O2`, `-DLZ4_FREESTANDING=1`; no fast-loop override. Inference: architecture-gated fast loop is absent in this wasm build. Not independently confirmed by disassembly in this survey.
- [Fast-loop source:2071–2209](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2071-L2209) remains useful context: `Main fastloop assertion: We can always wildcopy FASTLOOP_SAFE_DISTANCE`; it uses `LZ4_wildCopy32`, large output margins, special small-offset helpers. Do not spend the spike proving it if the compiled artifact omits it.

### Safe-loop path map

| path | exact upstream excerpt | proof consequence (inference) |
|---|---|---|
| Empty output / empty input | [2064–2069](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2064-L2069): `return ((srcSize==1) && (*ip==0)) ? 0 : -1;` / `if (unlikely(srcSize==0)) { return -1; }` | R2's zero-capacity exception is implementation-specific and necessary. Short-circuit order matters for R1 when source size is zero. |
| Entry and token split | [2214–2218](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2214-L2218): `while (1)` / `assert(ip < iend);` / `token = *ip++;` / `length = token >> ML_BITS;` | Main invariant must establish readable next token on every re-entry; asserts are documentation, not assumed theorem premises. |
| Two-stage shortcut | [2051–2052](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2051-L2052): `shortiend = iend - 14 /*maxLL*/ - 2 /*offset*/;` / `shortoend = oend - 14 /*maxLL*/ - 18 /*maxML*/;`; [2230–2255](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2230-L2255): `(length != RUN_MASK)` and `(ip < shortiend) & (op <= shortoend)`, then `LZ4_memcpy(op, ip, 16)`; match guard `(length != ML_MASK) && (offset >= 8) && ... match >= lowPrefix`, then copies `8`, `8`, `2` bytes. | Literal/match logical lengths can be shorter than physical stripes. Sequential stripes can implement an overall overlapping match even when `offset >= 8`; do not strengthen that guard to offset ≥ full match length based on the source's loose comment `Do not deal with overlapping matches.` Prove non-overlap per memcpy stripe + recurrence across stripes. |
| Length extension | [1979–2013](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L1979-L2013): `s = **ip; (*ip)++; length += s;`, `while (s == 255)`, `if (unlikely((*ip) > ilimit)) ...`, `if ((sizeof(length) < 8) && unlikely(length > ((Rvl_t)(-1)/2))) ...`. Literal call [2264–2270](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2264-L2270): `read_variable_length(&ip, iend-RUN_MASK, 1)`; match call [2345–2351](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2345-L2351): `read_variable_length(&ip, iend - LASTLITERALS + 1, 0)`. | Invariant = consumed extension bytes, exact accumulated sum, pointer bounds + machine-width arithmetic, all prior continuation bytes maximal. Initial-check flag differs: match call relies on caller-established margin. Check-before/after-read ordering must be modeled exactly. |
| Literal terminal vs wild-copy path | [2279–2333](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2279-L2333): `(cpy>oend-MFLIMIT) || (ip+length>iend-(2+1+LASTLITERALS))`; full terminal case requires `(ip+length != iend) || (cpy > oend)` false; then `LZ4_memmove(op, ip, length)` and break. Else `LZ4_wildCopy8(op, ip, cpy)`. | Terminal success consumes exactly the full input; this is central to R3. Nonterminal path reserves offset/token/trailing-literal input and output margins for speculative copies. |
| `wildCopy8` | [463–472](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L463-L472): `customized variant of memcpy, which can overwrite up to 8 bytes beyond dstEnd`; body `do { LZ4_memcpy(d,s,8); d+=8; s+=8; } while (d<e);` | Physical access summary must include whole stripes and the mandatory first iteration even for an empty logical copy. Corrected `op=cpy` is not the write footprint. Proof may use a tighter derived bound, but source's documented bound is the conservative one quoted here. |
| Offset validation | [2356](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2356): `if ((checkOffset) && (unlikely(match + dictSize < lowPrefix))) goto _output_error;` | In no-dictionary specialization validates match not before destination start. Does not reject zero offset; R3 must use its specified zero-fill exception. |
| Small offset | [474–475](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L474-L475): `static const unsigned inc32table[8] = {0, 1, 2,  1,  0,  4, 4, 4};` / `static const int      dec64table[8] = {0, 0, 0, -1, -4,  1, 2, 3};`; [2406–2419](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2406-L2419): first `LZ4_write32(op, 0)`, then four byte assignments, table-adjusted `LZ4_memcpy(op+4, match, 4)`, table correction; else an eight-byte copy. | Finite offset cases make a local lemma practical. Preserve sequential-write/read semantics: offsets within the first stripe intentionally read bytes just written. Zero-offset initialization is semantically relevant, not removable as a sanitizer-only detail. |
| Match near output end | [2421–2434](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2421-L2434): `cpy > oend-MATCH_SAFEGUARD_DISTANCE`; then `oCopyLimit = oend - (WILDCOPYLENGTH-1)`, `if (cpy > oend-LASTLITERALS) ...`, a bounded wild copy + `while (op < cpy) { *op++ = *match++; }`; far case copies another stripe and optional wild copy; finally `op = cpy`. | Show initial stripe remains inside capacity *before* later error check. Last byte loop uses forward overlap semantics. Keep logical decoded prefix and actual copied region as different invariants. |
| Exit | [2439–2443](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L2439-L2443): success `return (int) (((char*)op)-dst);`; error `return (int) (-(((const char*)ip)-src))-1;`. | R1 covers both exits, regardless of partially modified output. R3 concerns nonnegative success and requires signed-return / bounded pointer-distance arithmetic. |

Constant source [241–248](https://github.com/lz4/lz4/blob/v1.10.0/lib/lz4.c#L241-L248), verbatim:

```c
#define MINMATCH 4
#define WILDCOPYLENGTH 8
#define LASTLITERALS   5
#define MFLIMIT       12
#define MATCH_SAFEGUARD_DISTANCE  ((2*WILDCOPYLENGTH) - MINMATCH)
#define FASTLOOP_SAFE_DISTANCE 64
```

Format anchors that the model/spec must preserve:
- [End of block conditions](https://github.com/lz4/lz4/blob/v1.10.0/doc/lz4_Block_format.md#end-of-block-conditions): `The last sequence contains only literals`; `The last 5 bytes of input are always literals`; `The last match must start at least 12 bytes before the end of block`; `When a block does not respect these end conditions, a conformant decoder is allowed to reject the block as incorrect.` That last sentence permits rejection, not a requirement that every decoder reject every violation; R3's permitted relaxation remains explicit.
- [Safe decoding](https://github.com/lz4/lz4/blob/v1.10.0/doc/lz4_Block_format.md#safe-decoding): `Always ensure that read and write operations remain within the limits of provided buffers.` Zero-offset case: `the reference LZ4 decoder clears the match segment with 0 bytes`.
- Same section: `when matchlength is larger than offset ... some of the later bytes to copy do not exist yet, and will be generated during the early stage of match copy operation.` Hence neither snapshot memcpy nor snapshot memmove is a correct general match spec.

## Coverage / verification limits

This is a primary-source/textual survey. No upstream Lean/Coq/Isabelle/HOL proof build or FVA gate was run; no binary disassembly was independently counted. Reported effort/performance numbers remain attributed source claims. Exact upstream theorem signatures and code guards were inspected in pinned source snapshots; those observations establish what is stated, not that the entire imported trust closure is sound. Negative search results are bounded by search indexing and the named places/queries, not proofs of absence. The full-index LZ4 status count and Talos line/token scans are the only local measurements in this report.

researcher-3-DONE-1
