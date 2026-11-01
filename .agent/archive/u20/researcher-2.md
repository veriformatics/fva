# researcher-2 — method B: refinement of compiled code to a functional model (simulation relations, model reuse, effort)

Completed cells = evidence + limits; no unresolved seed cells. Each number/quote/conclusion carries URL or file:line + a verbatim excerpt. Validator target = zero literal unknown cells.

| id | question | answer | numbers | source (URL + verbatim excerpt) | applicability to FVA (Lean 4.35 + Mathlib; axioms = propext, Classical.choice, Quot.sound ⇒ no native_decide, no bv_decide; Wasm small-step `Step` + verified stepper `Ref.step`) |
|---|---|---|---|---|---|
| R2.1 | Projects proving compiled/low-level code refines a functional model (seL4 binary↔C, CompCert passes, Vale/EverCrypt, Jasmin, Aeneas (Rust→Lean), CN, Low*, Bedrock2/Rupicola, Fiat Crypto): how the simulation relation is stated for loops over memory, at which granularity (instruction, block, iteration) | **Relation = abstract values + concrete representation, at loop/phase boundaries; local operations discharge lower-level effects.** Rupicola instantiates representation predicates with partial functional execution (`iter i …`, mapped prefix + untouched suffix); algorithmic bounds become model lemmas. liblzma/VST models abstract decoder transitions, then funspec/reps tie them to C structs/buffers, and symbolic body proofs preserve a phase-coupled invariant. Lean-zip uses logical-prefix equality between append-only output and a presized cursor buffer. These are model-refinement exemplars; Rupicola **generates** code, not validates arbitrary clang output. | No new generic speedup ratio. Refinement granularity = iteration/phase/block; machine effects still need load/store/branch/call rules. | [Rupicola PLDI22 §§3.2–3.4](https://adam.chlipala.net/papers/RupicolaPLDI22/RupicolaPLDI22.pdf): “instantiating the state representation predicate with symbolic variables that represent the program’s state partway through iteration”; “map f (first n l) ++ (skip n l)”; [liblzma §3.1](https://arxiv.org/html/2608.29716v1#S3): “A Spec then adds VST representation predicates that relate those values to C structs and buffers”; [Lean-zip pinned source](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L14-L20): “its logical content is `buf.extract 0 outPos`”. | **Inference:** keep FVA’s reviewed format relation distinct from an unreviewed algorithm model; relate model cursors/prefix/phase to machine locals + control position + memory projection. Model-correctness can be instruction-free; simulation cannot. Use exact concrete memory as an input to lower-level block summaries, then project only the prefix needed by the model at cutpoints. |
| R2.2 | How the model is written for an algorithm with speculative over-reads/over-writes (wild copies) and overlapping copies (LZ77 back-references): exact-memory model vs abstract model + relation; examples (DEFLATE/zlib/zstd/brotli/LZ4 verifications, memcpy/memmove proofs) | **Use abstract valid prefix + concrete scratch-capacity relation, not exact whole-memory equality with the format model.** Lean-zip actually proves fixed-capacity cursor refinement to growing-output reference and a masked wide-copy optimization; overlap is a forward evolving-output recurrence. For snapshot memmove, Bedrock2 uses two nonseparating views of the same initial heap, with distinct source/destination frames and only the destination frame preserved. These are different copy contracts. **None-found, bounded:** an inspectable completed optimized LZ4 wildcopy→functional-model proof; queried exact wildcopy/wild-copy combinations and prior survey corpus (§R2.2). | Lean-zip’s wide short-match lemma requires `8 ≤ distance`, `0 < len`, `len ≤ 8`, and `destOff.toNat + 8 ≤ a.size`; its full wide store preserves extra bytes by masking. This is not arbitrary-overcopy LZ4. | [Lean-zip `InflateFastCorrect.lean:453–457`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L453-L457): `(hdistance : 8 ≤ distance) (hlenpos : 0 < len) (hlen : len ≤ 8)` / `(hroom : destOff.toNat + 8 ≤ a.size)`; [PLDI24 §2.3](https://adam.chlipala.net/papers/GarageDoorPLDI24/GarageDoorPLDI24.pdf): “only the frame R of the destination buffer is preserved in the postcondition”; “The source frame Rs is intentionally unused”. | **Inference:** wildcard tail contents belong to simulation’s concrete-memory witness, not the reviewed LZ4 output. Preserve prefix and input bytes that future parsing needs; separately prove each physical access stays in capacity. An eight-byte snapshot copy can summarize one stripe when source/destination for that stripe are disjoint; sequential stripes may still overlap overall and must compose via updated memory. Never replace LZ77 forward expansion by snapshot memmove. |
| R2.3 | Reported model reuse across compiler versions / optimization levels / source releases (what survives: model, model theorems; what is redone: simulation) and its measured cost | **No external quantified cross-compiler re-proof-cost result found** after fresh query variants + seL4’s newer binary-verification talk; named searches in §R2.3. Latest inspected seL4 talk describes compiler-progress maintenance and a replacement checker/search implementation in progress, not free reproof. Local FVA checkpoint supplies actual, narrowly scoped reuse evidence: model + model theorem survived the optimization change unchanged, concrete simulation was rewritten. | Local historical observation, not rerun: R reused 68 model code lines; new -O1 machine-facing proof = 170, binding/composition = 59; first R repair 7.4 min. Copy/order confounding prevents superiority inference. | [FVA E1 M0/M1 + bounded findings](/home/eturkes/Projects/fva/.agent/archive/u19/e1.md): “`extModel`, `ModelOK`, `model_ok` reused unchanged”; “R reused its 68-line model package and added 59 lines of binding/composition plus a new machine-facing proof”; [seL4 2025 slides 54–55](https://sel4.systems/Summit/2025/slides/binary-verification.pdf): “Account for progress in GCC”; “Status: check phase complete, still working on search phase”. | **Inference:** stability boundary is credible, its net cost advantage unmeasured. Shared abstract format/model theorems can persist; locals/CFG/stripe/call summaries remain artifact-specific. Verified-compiler projects avoid repeating an artifact proof through a generic compiler theorem, but FVA’s unchanged arbitrary clang Wasm does not come with that theorem. |
| R2.4 | Effort data: model + simulation + model-correctness proof sizes and person-time for comparable decoders/parsers (the larger the better) | **Fresh comparable decoder evidence: liblzma/VST functional model → representation predicate/funspec → body proof.** Large model-relative proofs do not make the machine-facing correspondence cheap. Authors report substantial duplicated invariant/postcondition reconstruction; modular child contracts kept the outer decoder much smaller. Source-level, transformed C; partial correctness, not binary/RFC correctness. PLDI24’s separate memmove/crypto-refinement costs and their denominators appear in §R2.4. | `lzma_decode`: 338 source C SLoC; 183,268 proof SLoC (excludes shared helpers + generated goals). `lzma2_decode`: 98 / 5,643. Functional models + range-decoder well-formedness = 3,684 SLoC across development. 1,595 agent sessions / 70 days; **not human effort or labor savings**, no baseline. | [paper §§3.1, 6.2–6.4](https://arxiv.org/html/2608.29716v1#S6): “A functional Model gives executable Rocq definitions of a routine’s abstract state and transition”; “lzma_decode \| 76 \| 183,268 \| 338”; “lzma2_decode \| 144 \| 5,643 \| 98”; “3,684 in functional models and the range-decoder well-formedness development”; “1,595 agent sessions over the 70-day lzma_decode development interval”; “These figures characterize scale and observed outcomes, not human effort or labor savings; no human-only baseline is available.” Exact context in §R2.4. | **Inference:** strongest newly found decoder-effort warning: account for model + representation/invariant + every exit, not model size alone. Avoid forecasting Lean/Wasm costs from these source-reported Rocq counts. FVA cannot adopt its source normalizations as a substitute for linking unchanged Wasm. |
| R2.5 | Total correctness + per-step footprints under refinement: how projects obtain termination and "every reachable state accesses only X" (not just final-state frames) through a simulation | **They are separate obligations unless built into the simulation’s judgment.** Bedrock2/Rupicola’s loop logic is total; abstract iterations carry bounds, concrete operation lemmas establish safety. liblzma’s `semax_body` is explicitly **partial** and not a trace/total theorem. Standard CompCert traces observe syscalls/volatile accesses/annotations, **not all ordinary memory accesses**, so trace refinement alone is not R1. FVA already has the stronger local composition interface: universal-successor `Until` with `Within`, then `mustW_of_until` to carry every reachable access through model/loop exits. | A stuttering simulation needs well-founded descent for zero-target-step cases; model termination alone does not exclude arbitrary concrete stuttering. No sourced generic bound or percentage saving. | [Rupicola Box 2](https://adam.chlipala.net/papers/RupicolaPLDI22/RupicolaPLDI22.pdf): “the semantics only give meaning to terminating loops, so proofs about Bedrock2 programs are total-correctness proofs”; [liblzma §2.1](https://arxiv.org/html/2608.29716v1#S2): “does not by itself establish termination, total correctness, trace refinement”; [CompCert Events](https://compcert.org/doc/html/compcert.common.Events.html): “A volatile load from a global memory location”; `volatile_load … E0 v`; [FVA `Footprint.lean:21–28,224–239`](/home/eturkes/Projects/fva/FVA/Proof/Lib/Footprint.lean): `Must H Q c ∧ Throughout H (Within R W) c`; `∀ c', Step H c c' → Until H P Q c'`. | **Inference:** refine by total block/iteration summaries returning a new model-related cutpoint, with `Within` on every interior configuration. Compose via `Until.trans`, induct on model measure, and close every exit into `MustW`. This reuses current proof law and respects Wasm nondeterminism; outcome equality/final-memory frames alone do not discharge R1. |
| R2.6 | Lean 4 idioms for stating and proving a simulation between a small-step machine and a recursive model (well-founded recursion, fuel, `termination_by`, `Nat.strongRecOn`), with examples in public Lean 4 code | **Functional induction over the algorithm’s generated `.induct` recursor** carries branch guards and recursive hypotheses at precisely the recursive calls; prove buffer views as operation lemmas, then lift through block loops. Lean-zip demonstrates both forward and reverse cursor/reference simulations. **Small-step compiled-code example:** `ship-your-interpreter` separates loading relation, forward termination simulation, and no-source-behavior case; determinism is explicitly used to recover the reverse behavior implication. Both refine relations, not just compute fixed fuel. See §R2.6 exact signatures and limits. | Lean-zip declares `termination_by len - k` for overlap-copy recursion and `(data.size - pos.toNat) * 9 + cnt.toNat` for the fast decoder. Its cursor proof uses `induction … using goCur.induct`; machine example’s runtime proof is not replayed here. | [Lean-zip `InflateFast.lean:62–67,226`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Native/InflateFast.lean#L62-L67): `termination_by len - k`; [correspondence:629–644](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L629-L644): `induction pos, bitBuf, cnt, buf, outPos using goCur.induct`; [RISC-V `Vsa/Lang/Basic.lean:13–16,39–42,52–61`](https://github.com/BasisResearch/ship-your-interpreter/blob/fb07094cff916318c34b07494a7d739f1e53989b/Vsa/Lang/Basic.lean#L13-L16): “With machine determinism it yields `Lang.refinement`”; `obtain ⟨rfl, rfl⟩ := h.deterministic …`. | **Inference:** FVA can retain its existing `Until`/`MustW` machine proof, using model `.induct` or measure induction only to orchestrate block summaries. No new proof assistant/library dependency is needed. For Wasm nondeterminism, keep universal-successor premises (`Until.next`) rather than importing a deterministic outcome-only theorem. Fuel alone needs an adequate-fuel theorem and can hide missing totality. |
| R2.7 | Does a functional model itself reduce FVA’s human-review surface? | **Not automatically.** liblzma explicitly human-reviews models/funspecs and proves model-relative body correctness; a large model used as the specification would become review burden. FVA’s existing design is different: model is proof support, outside the claim/import surface, with a separate proof to the declarative claim. Preserve that boundary when growing from one loop to the whole decoder. | No measured reduction in human-review time or total trusted specification for this route found in the new sources. Source/proof LOC are not readability measurements. | [liblzma §3.1](https://arxiv.org/html/2608.29716v1#S3): “Humans review and approve the models and funspecs”; [FVA contract:22](/home/eturkes/Projects/fva/docs/contracts/U19-decoder-spike.md:22): “the model is never imported by a spec module”; [FVA `ExtRefine.lean:264,311–333`](/home/eturkes/Projects/fva/FVATest/Subjects/Lz4C/ExtRefine.lean:264): `theorem model_ok`; `theorem ext_l1 : ExtL1`. | **Inference:** choose model convenience without promoting it to the trusted endpoint. The deliverable must still prove the small declarative LZ4 relation about the byte-linked Wasm, with error/acceptance behavior, termination and footprint. Method B and block summaries are composable; B does not remove instruction-level correctness obligations. |

## Detail (keyed by row id)

Scope = gap-filling: functional/exact-memory model boundary; overlap + wild-copy refinement; measured reuse/effort; totality + access preservation. Prior results remain baselines, not fresh evidence. Upstream proof code will be read, not built/replayed.

Prior survey = `.agent/archive/u19/researcher-{1,2,3}.md`; its HOL4/seL4/CompCert/s2n/LNSym/Talos/Aeneas overview is not repeated. Local baseline = `.agent/archive/u19/e1.md`, not a new experiment. Local source revision read = `e5de229ded1e512e7da5996a5d4f0cb782b8a9a6`.

## R2.1 — relation + granularity: what is factored out

**Rupicola: partial functional execution instantiates the concrete invariant.** [PLDI22 §§3.2–3.4, PDF pp.7–10](https://adam.chlipala.net/papers/RupicolaPLDI22/RupicolaPLDI22.pdf):

> “The first part of this process (constructing and verifying a functional model) is done by hand”
>
> “the shape of the model, combined with the lemmas introduced into the relational compiler, determines what code gets generated.”
>
> “we create a closed-form term parameterized by the (symbolic) iteration number and let users reason directly about it.”
>
> “our lemma that connects map to a for loop exposes intermediate states of the form map f (first n l) ++ (skip n l).”

Pinned concrete instance: [`mit-plv/rupicola@d33f7024a7a03c9e0f05f746dff8434d450a4f6e`, `src/Rupicola/Lib/Loops.v:2228–2275`](https://github.com/mit-plv/rupicola/blob/d33f7024a7a03c9e0f05f746dff8434d450a4f6e/src/Rupicola/Lib/Loops.v#L2228-L2275). Verbatim excerpts:

```coq
Lemma compile_scalar_fold_left: forall [tr mem locals functions],
...
let a' := List.fold_left f (List.firstn n bs) a in
loop_pred idx a' tr mem locals ->
...
body_impl
<{ lp idx (f' a' idx) }>
```

`loop_pred` carries the representation of the partially folded abstract accumulator in actual trace/memory/locals. Each body proof updates it; the loop lemma quantifies the iteration count. **Boundary:** generated imperative code + verified compilation, not an automatic correspondence proof for arbitrary existing optimized code. FVA can reuse the invariant idea without adopting Rupicola’s code-generation contract.

**liblzma: model transition → representation predicate → body theorem.** [Paper §3.1](https://arxiv.org/html/2608.29716v1#S3):

> “A functional Model gives executable Rocq definitions of a routine’s abstract state and transition.”
>
> “A Spec then adds VST representation predicates that relate those values to C structs and buffers, and a standard VST funspec whose postcondition requires the C outcome to agree with the model.”

[§4](https://arxiv.org/html/2608.29716v1#S4):

> “The VST proof establishes a loop invariant before the first iteration and re-establishes it after every continuation.”
>
> “Treating the outer phase and child stage independently admits combinations that no execution of the C program can reach.”

Inference: a functional model does not eliminate a representation invariant; it gives that invariant a denotational component. Decoder phases and child/copy states still need coupling facts. A model that mirrors code but omits reachability coupling can make simulation obligations unprovable even when its standalone transitions look plausible.

**Lean-zip: algorithm-level projection rather than identical memory.** [`InflateFastCorrect.lean:14–20`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L14-L20):

> “the reference threads a growing `output` whose `.size` is the logical output length; the cursor loop threads a fixed-size buffer plus a cursor `outPos`, and its logical content is `buf.extract 0 outPos`.”

Concrete theorem [`:629–641`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L629-L641) requires reference success on `(buf.extract 0 outPos.toNat)` and concludes:

```lean
∃ cf, goCur ... buf outPos = .ok (cf, rf.size.toUSize, rp, rb, rc) ∧
  cf.extract 0 rf.size = rf
```

Inference for FVA = a concrete machine/cutpoint relation whose abstract output is the valid destination prefix; actual bytes outside that prefix remain concrete state, not fictitious output. Lower-level block summaries can remain exact-memory transformers. The abstract LZ4-format proof need not mention scratch-tail values.

## R2.2 — overlap + speculative-copy boundary

### Actual abstract-overlap model in an archived production-decoder proof

Artifact = [Zenodo `22166622`, `supplementary.zip`](https://zenodo.org/records/22166622), member `main/src/liblzma/lz/lz_decoder/model_window.v:8–23,53–65`. Published metadata `md5:33b9441b282d4a8e669321f8d79b94f1`; downloaded archive’s `md5sum` matched. Verbatim model excerpts:

```coq
Record sliding_window := create {
    log: list Z;
    free: nat;
}.
Definition get (w: sliding_window) (distance: Z): Z :=
    Znth distance (log w).
...
| S n =>
    match put_safe w (get w distance) with
    | None => (w, 0)
    | Some w' =>
        let '(resulting_window, bytes_written) := repeat' w' distance n in
        (resulting_window, bytes_written + 1)
```

`put_safe` pushes the new byte onto `log`, then recursion reads the **updated** window. This directly models overlapping repetition. It is not a snapshot of the original source slice. The reversed-log index convention is LZMA-specific: the source’s distance/index must be translated deliberately before adapting it to LZ4’s offset vocabulary.

Concrete representation, archive member `main/src/liblzma/lz/lz_decoder/spec.v:29–46,56–73`:

```coq
Definition buffer_rep (w: sliding_window) (effective_size: Z) (pos: Z) (ptr: val): mpred :=
...
data_at Ews (tarray tuchar size)
    (upd_Znth (pos - 1)
        (rev (sublist 0 pos padded) ++
         rev (sublist (pos - lz_dict_repeat_max) (size - lz_dict_repeat_max) padded))
        (Vint (Int.repr (get w 0)))) ptr.
```

`padded_log_bytes`, model member `:485–487`:

```coq
map (fun x => Vint (Int.repr x)) w.(log) ++
    Zrepeat Vundef (effective_size + 2 * lz_dict_repeat_max - Zlength w.(log))
```

`dict_repeat_spec`, spec member `:443–473`, relates C’s resulting buffer/struct through `sliding_window_rep_at` and requires:

```coq
(w', written) = repeat w distance len;
0 <= written <= len;
```

This is concrete evidence for **abstract history + representation of an allocated ring buffer**, including spare/uninitialized capacity; it is not a proof of LZ4’s speculative wide accesses. Wasm bytes have their own fully defined semantics, so FVA’s scratch witness should use arbitrary actual bytes, not transplant CompCert’s `Vundef` meaning.

### Snapshot memmove needs a different contract

[PLDI24 §2.3, p.7](https://adam.chlipala.net/papers/GarageDoorPLDI24/GarageDoorPLDI24.pdf), exact pre/post excerpt:

```text
requires t m := m =* bytes src s * Rs ∧ m =* bytes dst d * R ∧ ...
ensures t' m := m =* bytes dst s * R ∧ t=t'
```

> “separate frame quantifiers (R and Rs) in the two non-separating conjuncts asserted on the same memory (m =*)”
>
> “only the frame R of the destination buffer is preserved in the postcondition.”
>
> “The source frame Rs is intentionally unused in the postcondition to indicate that it may not be preserved.”

Inference: use two overlapping views when a routine guarantees source-snapshot semantics; use evolving-window recurrence when it guarantees forward LZ77 propagation. Do not use a generic ISO `memcpy` contract to erase the compiled shim’s actual ordering/alias behavior. FVA’s contract already distinguishes these: `/home/eturkes/Projects/fva/docs/contracts/U19-decoder-spike.md:60` says “forward-overlap repetition ≠ `memmove`'s source-preserving result”.

### Wide copies: nearest checked Lean example, exact limitation

[`Zip/Native/InflateFast.lean:95–111`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Native/InflateFast.lean#L95-L111):

> “The destination word is blended into the bytes above `len`, so the wide store changes exactly the logical match bytes.”
>
> “Limiting this path to one exact store preserves the fastloop's whole-buffer invariant; longer and overlapping matches use `copyWithinAtU`.”

The implementation loads both source and destination words and writes:

```lean
let mask := (0xffffffffffffffff : UInt64) >>> ((8 - len).toUInt64 <<< 3)
a.usetUInt64LE destOff ((src &&& mask) ||| (dst &&& ~~~mask)) hroom
```

Its equality proof [`InflateFastCorrect.lean:453–513`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L453-L513) splits each byte of the physical word between logical match bytes and preserved tail bytes. Bounds include the **whole** word, even when the logical copy is shorter. This supports word/byte bridge lemmas and prefix projection; it does **not** support claiming that LZ4’s unmasked wildcopy preserves its entire logical tail.

**Inference for actual LZ4 wildcopy:** track (a) correct decoded prefix; (b) actual scratch bytes and capacity; (c) framed bytes outside allowed writes; (d) each physical load/store range. After each stripe, recompute the next stripe’s source view from the updated concrete memory. An overall overlapping match can consist of locally non-overlapping stripes; neither whole-match disjointness nor snapshot-copy semantics is justified merely by a stripe’s non-overlap.

**None-found, bounded:** completed inspectable optimized LZ4 wildcopy→functional-model simulation with access footprints. Places searched = prior FVA survey corpus, Lean-zip code, liblzma paper/artifact, Rupicola/Bedrock2 papers/code, WebSearch-indexed scholarly/GitHub results. Fresh query variants: `"functional model" "wildcopy" verification OR verified OR proof`; `"wildcopy" "proof" "Lean" OR "Coq" OR "Isabelle"`; `"verified" "decoder" "model" "wild copy"`; `"LZ4" "refinement" "proof"`; `"wildcopy" "verification" OR "verified"`. Hits were the already-known compression projects, source-code changes/CVE discussions, or unrelated uses of “verified”. No nonexistence claim; no unpublished/private work examined.

## R2.3 — reuse: stable endpoint, unstable correspondence

Fresh external search did not yield a measured compiler-version/optimization transition with model-proof reuse and timed simulation repair. Inspected primary updates = [seL4 binary-verification talk abstract](https://nickspinale.com/talks/sel4-summit-2025.html) + [slides 54–55](https://sel4.systems/Summit/2025/slides/binary-verification.pdf):

> “Account for changes to seL4”
>
> “Account for progress in GCC”
>
> “Status: check phase complete, still working on search phase”

This is an engineering-maintenance report, not quantified cost and not evidence that the abstract specification survives every semantic source change. The older seL4 compiler-version caveat is already in the prior survey; the newer talk does not close its measurement gap.

Local measured baseline, `/home/eturkes/Projects/fva/.agent/archive/u19/e1.md:20,31,59,65`:

> “R repair (-O1, first) | 7.4 | new stepping script + `locals_at` tactic; `extModel`, `ModelOK`, `model_ok` reused unchanged”
>
> “R reused its 68-line model package and added 59 lines of binding/composition plus a new machine-facing proof”
>
> “the second implementation was quicker in both phases, with documented copying of the earlier script; route and carryover effects cannot be separated in this case study.”

`M1`’s R -O1 row separately reports `170` stepping/simulation code lines. These are historical measurements; this survey did not rerun a build or author a repair. They demonstrate reuse of an algorithm package, not lower total repair cost. No minimality result, next-compiler forecast, or causal route advantage follows.

Fresh query variants: `"functional model" "compiler versions" "proof"`; `"refinement" "proof reuse" "compiler" "versions" binary`; `"verification" "recompilation" "functional model"`; `binary verification refinement "compiler" "hours" "maintenance" proof`; `"seL4" "gcc" "fine-tuning" compiler versions proof`; `"binary verification" "GCC 10" OR "GCC 12" OR "GCC 13"`. Later queries surfaced the same seL4 papers/talk or unrelated compiler/proof-reuse work. Searches were bounded engine results, not a complete history of every prover/repository.

Inference: separate model→format theorems, concrete block effects, and block→model correspondence. A compiler change may preserve the first while replacing the latter two. Verified-compiler projects amortize the link via one generic compiler theorem; that is a different starting asset from FVA’s arbitrary clang-produced artifact.

## R2.4 — comparable effort, with denominators + trust boundary

### liblzma: the closest newly inspected real decoder

Primary = [paper §6.2, Table 2 + proof-size accounting](https://arxiv.org/html/2608.29716v1#S6.SS2). Verbatim rows:

```text
Name          Spec  Proof     C
lzma_decode   76    183,268   338
lzma2_decode  144     5,643    98
dict_repeat   31      2,081    47
```

Source defines the count:

> “Each row specifies source lines of code without empty and comment-only lines: its funspec definition, attributed proof file or files, and C function body.”
>
> “Shared models and lemmas in other files, generated Clight ASTs (code.v), and generated goal-statement files (_goal.v) are not counted in the table.”
>
> “3,684 in functional models and the range-decoder well-formedness development”

Thus `183,268` is neither the total development nor a machine-code proof-size denominator. The same accounting lists `775,768` generated goal lines and `39,760` shared helper lines; these are separate categories, not included in that row. Source quote:

> “775,768 in generated _goal.v files stating extracted proof obligations”; “plus 39,760 in helper libraries shared across those extracted proofs”.

[§6.3](https://arxiv.org/html/2608.29716v1#S6.SS3):

> “1,595 agent sessions over the 70-day lzma_decode development interval”
>
> “Finer-grained accounting of session outcomes, human review, active agent-hours, and service cost would require recovering and auditing interaction logs that were not available for this paper.”
>
> “These figures characterize scale and observed outcomes, not human effort or labor savings; no human-only baseline is available.”

**Observed costs behind the counts**, [§6.2](https://arxiv.org/html/2608.29716v1#S6.SS2):

> “only about 2% of the lines in the 28 extracted proofs are forward steps.”
>
> “Roughly 42% of the lines instead belong to blocks repeated verbatim across multiple proofs.”
>
> “an 18-conjunct decoder-state well-formedness argument, written out 63 times to re-establish the loop invariant.”
>
> “lzma2_decode stays small because it delegates LZMA1 decoding to a function with a VST specification.”

Inference: in this development, reducing instruction stepping alone would miss the dominant textual duplication. Reusable state-validity reconstruction, call contracts and shared exit summaries are independent scaling work that either direct or refinement proofs need. The percentages measure source-text categories, not elapsed proof-engineering time or Lean runtime.

**Totality/link/axiom limits**, [§2.1 + §§6.2–6.4](https://arxiv.org/html/2608.29716v1#S2.SS1):

> “It does not by itself establish termination, total correctness, trace refinement, or compatibility between separately maintained caller and callee contracts.”
>
> “the malloc and free body lemmas are declared as Rocq Parameters, and an axiom (mem_mgr_rep) introduces the memory-manager predicate.”
>
> “applying the result to upstream liblzma additionally requires source equivalence.”

It verifies a structured, transformed C snapshot; it does not supply FVA’s unchanged compiled-artifact link or admissible axiom closure. No model→independent-format correctness effort split is reported in the inspected §3.1/§6 inventory: the result is explicitly **model-relative**.

### Smaller helper with explicit human-time report

[PLDI24 §3.2, pp.10–11 + §4.3.1, p.19](https://adam.chlipala.net/papers/GarageDoorPLDI24/GarageDoorPLDI24.pdf):

> “specification and proof of memmove (2 days)”
>
> “memmove (350 and 21 lines)”

Context identifies proof lines then implementation lines. This is a handwritten Bedrock2 helper, not measured clang/Wasm repair; useful evidence that a reusable overlap-correct helper is nontrivial and can be much smaller than a whole decoder proof.

### New-domain refinement overhead can dominate the model

Same paper, Table 3, p.19 (visually inspected):

```text
Purpose                         ChaCha20  Montgomery ladder
High-level algorithm                 40                 84
Main proofs                         663                550
Rupicola lemmas & extensions        1282                132
Generic lemmas & automation          558                222
```

Authors qualify: “These numbers are not exact since work on both implementations involved some improvements to existing systems”. Their §3.5 explanation:

> “shifting between by-word and by-byte views of data required significant manual effort.”
>
> “programs that trigger this behavior tend to require extensive supplemental proof effort.”

Inference: for FVA, word/byte memory bridges and existing block-support fit matter at least as much as having a pleasant recursive model. These are crypto/generated-code examples, not a decoder effort estimate or controlled comparison.

## R2.5 — total simulation + all-prefix accesses

**Standard simulation diagrams need progress as well as state agreement.** [CompCert `Smallstep`, `fsim_properties`](https://compcert.org/doc/html/compcert.common.Smallstep.html), verbatim declaration components:

```coq
fsim_order_wf: well_founded order;
...
(Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
/\ match_states i' s1' s2'
```

A finite segment per model transition is not enough, by itself, to constrain **all** concrete executions: determinism or a universal-successor/backward argument must close that gap. Likewise a source→target forward existence theorem does not make every implementation loop terminate merely because the model is a total Lean function.

**CompCert trace refinement is not an ordinary-access footprint theorem.** [Official `Events`](https://compcert.org/doc/html/compcert.common.Events.html):

> “the only requirement is that they do not expose memory states nor pointer values (other than pointers to global variables), because these are not preserved literally during compilation.”

Its event constructors enumerate syscall, volatile load, volatile store, annotation. The nonvolatile rules explicitly return the empty trace:

```coq
Mem.loadv chunk m (Vptr b ofs) = Some v ->
volatile_load ge chunk m b ofs E0 v.
...
Mem.storev chunk m (Vptr b ofs) v = Some m' ->
volatile_store ge chunk m b ofs v E0 m'.
```

Inference: ordinary read/write-address bounds cannot be transported merely by equality of these I/O traces. Need an enriched observation or a concrete-step safety invariant. This is why generic “refinement preserves safety” must name the safety property and semantics it preserves.

**FVA already has the needed judgment.** `/home/eturkes/Projects/fva/FVA/Spec/Exec/Access.lean:58–66`:

```lean
def Within (R W : Nat → Nat → Prop) (c : Config) : Prop :=
  (∀ ma a, Reads c ma a → R ma a) ∧ (∀ ma a, Writes c ma a → W ma a)
def Throughout (H : HostSem) (P : Config → Prop) (c : Config) : Prop :=
  ∀ c', Steps H c c' → P c'
```

`/home/eturkes/Projects/fva/FVA/Proof/Lib/Footprint.lean:21–28`:

```lean
def MustW ... := Must H Q c ∧ Throughout H (Within R W) c
inductive Until ... where
  | done {c} : Q c → Until H P Q c
  | next {c} : P c → (∃ c', Step H c c') →
      (∀ c', Step H c c' → Until H P Q c') → Until H P Q c
```

`mustW_of_until` at `:224–233` requires an `Until H (Within R W) X c` proof and a `MustW` continuation for **every** `X` configuration; `Until.trans` at `:236–241` composes total segments. Thus FVA’s refinement can return a model-related cutpoint without losing access facts in the segment’s interior.

Inference, candidate whole-decoder structure: each abstract phase/iteration transition has a **total** concrete segment lemma under its representation invariant; each internal load/store proves `Within`; the exit preserves the representation and the concrete frame. Induct on the model’s decreasing measure; compose every normal/error exit into `MustW`. Keep the public `CallWithin` safety claim distinct from `CallReturns` termination, as `/home/eturkes/Projects/fva/docs/contracts/U19-decoder-spike.md:12–13,32–35` already requires.

## R2.6 — Lean implementation idioms worth reusing

### Functional induction fits an algorithm model; prove reverse acceptance separately

[`InflateFastCorrect.lean:629–645`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L629-L645) performs:

```lean
induction pos, bitBuf, cnt, buf, outPos using goCur.induct
```

The generated branch cases expose guards and recursive-call hypotheses. The loop’s measure is [`Zip/Native/InflateFast.lean:226`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Native/InflateFast.lean#L226):

```lean
termination_by (data.size - pos.toNat) * 9 + cnt.toNat
```

Importantly, forward correctness and accepted-input soundness are different theorem chains. [`InflateFastCorrect.lean:3890–3896`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L3890-L3896):

```lean
(href : Inflate.inflate data maxOut = .ok out) :
Inflate.inflateFastU data maxOut out.size = .ok out
```

Reverse [`:3920–3923`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Spec/InflateFastCorrect.lean#L3920-L3923):

```lean
(h : Inflate.inflateFastU data maxOut sizeHint = .ok o) :
Inflate.inflate data maxOut = .ok o
```

Inference: model→machine success resembles R2 but does not give R3 (“every accepted input has a format explanation”). Include the reverse/accepted-result direction in the correspondence contract from the outset. This Lean-zip result concerns Lean reference bodies; the same file `:91–94` says native C externs “are trusted (and conformance-tested) to refine” them. No claim that these are byte-linked machine proofs or that their dependency axioms match FVA.

### Public compiled-code simulation makes determinism reliance explicit

[`ship-your-interpreter@fb07094cff916318c34b07494a7d739f1e53989b`, `Vsa/Lang/Basic.lean:39–42`](https://github.com/BasisResearch/ship-your-interpreter/blob/fb07094cff916318c34b07494a7d739f1e53989b/Vsa/Lang/Basic.lean#L39-L42):

```lean
structure Sim : Prop where
  term : ∀ p c e out, Loaded p c → L.Fits p → L.Spec p e out → Halts c out e
  stuck : ∀ p c, Loaded p c → L.Fits p → (¬ ∃ e out, L.Spec p e out) →
    Diverges c ∨ ∃ out e, Halts c out e ∧ ¬ L.Obs e
```

Its reverse proof [`:52–61`](https://github.com/BasisResearch/ship-your-interpreter/blob/fb07094cff916318c34b07494a7d739f1e53989b/Vsa/Lang/Basic.lean#L52-L61) uses `h.deterministic` to identify the machine halt with the specified one. A source lacking behavior needs the separate `stuck` premise. `Lang.Total`/`SimTotal` [`:79–112`](https://github.com/BasisResearch/ship-your-interpreter/blob/fb07094cff916318c34b07494a7d739f1e53989b/Vsa/Lang/Basic.lean#L79-L112) add specified divergence and a trichotomy; the result permits divergence, so its name “total” is not a theorem that every program terminates.

The actual interpreter-loop rule [`VsaIris/Interp/LoopWhile.lean:447–477`](https://github.com/BasisResearch/ship-your-interpreter/blob/fb07094cff916318c34b07494a7d739f1e53989b/VsaIris/Interp/LoopWhile.lean#L447-L477) composes condition, body and recursive continuation, explicitly carrying source evaluation costs `(nc + nb + nr)`. Straight-line segment facts are declared earlier with `#ix_seg`. Useful architecture, but adding its Iris/Sail dependencies is outside FVA’s fixed stack. No build/replay/axiom audit of the repository was run here.

### Well-founded models: use equations, not expensive definitional reduction

[Lean 4.35 manual, Recursive Definitions, “Well-Founded Recursion”](https://lean-lang.org/doc/reference/4.35.0/Definitions/Recursive-Definitions/):

> “definitions that use well-founded recursion typically do not reduce definitionally. The reductions do hold as propositional equalities, however, and Lean automatically proves them.”
>
> “Even when the reduction behavior happens to hold definitionally, it is often much slower than structurally recursive definitions in the kernel, which must unfold the termination proof along with the definition.”

Inference: keep model proofs equation-driven; use the generated induction principle or explicit measure induction. Do not demand giant model reduction in a machine-state type. No performance advantage is asserted without a target measurement. FVA’s `/home/eturkes/Projects/fva/FVATest/Subjects/Lz4C/ExtRefine.lean:21–26,226–247` already uses `termination_by lim - (p + j)` and an explicit induction on that remaining bound.

## R2.7 — review-surface boundary + decision-relevant synthesis

[liblzma §3.1](https://arxiv.org/html/2608.29716v1#S3): “Humans review and approve the models and funspecs”. That review contract differs from FVA’s: `/home/eturkes/Projects/fva/docs/contracts/U19-decoder-spike.md:22` says “the model is never imported by a spec module”. `/home/eturkes/Projects/fva/FVATest/Subjects/Lz4C/ExtRefine.lean:264,311–333` proves `model_ok`, then composes it with simulation into the separately stated `ExtL1`.

**Inference, scoped judgment:** B is a sound decomposition candidate, especially for LZ77’s periodic-output reasoning and a format-level proof; the evidence does not establish that a whole-decoder functional model reduces total effort or replay cost versus direct stepping. The main costs remain concrete memory views, control-flow correspondence, alias/stripe lemmas and re-establishing coupled invariants at exits. Those costs can be addressed by block/callee summaries regardless of the high-level route. A hybrid — checked concrete summaries plus small model-level algorithm lemmas — is consistent with all inspected evidence. Literature supplies no defensible numerical effort ratio to rank the routes for this artifact.

## Coverage + checks

- Primary sources read = Rupicola PLDI22 paper + pinned loop lemma; Bedrock2/Rupicola/Fiat-Crypto integration PLDI24 paper; liblzma paper + published archived model/funspec sources; pinned Lean-zip optimized/reference correspondence; pinned RISC-V language/loop simulation; official CompCert simulation/events docs; Lean 4.35 recursion manual; newer seL4 talk/slides; local U19 proof/contract/results. No outside repository code was executed. Source revisions are pinned where available; CompCert web docs and seL4 talk are document URLs, not pinned code snapshots.
- Browser = own Neo tabs for paper/code access; ACM full text became readable through Neo after a direct `webtext` 403. A separate Jasmin ePrint PDF fetch returned HTTP 403; its claimed theorem was not used. No account/profile changes. Selected PDF pages/tables were visually inspected; text excerpts use `webtext`/`pdftotext` or exact source bytes, not search summaries.
- Source trust boundary = textual/source inspection, not proof replay. **Not run:** any FVA `lake`/`lean` build, gate, upstream proof build, independent kernel replay, new decoder proof, repair-cost benchmark, or end-to-end timing. Upstream effort counts remain attributed reports. The only local numerical checks used here are metadata/checksum equality, token/line locations and the deliverable’s cell validator; historical FVA timings remain historical.
- `none-found` rows name sources/queries; search indexing, shallow snapshots and selected relevant files limit coverage. No full history/fork census or unpublished work. No evidence that B’s correspondence is automatically cheaper for this Wasm decoder.
- Deliverable validation (actual stdout): `target_rows=7`; each row `columns=6`; `table_shape=PASS`, rc 0. Positive control: count 1, rc 0. Unknown-cell count: 0, grep rc 1 (normal no-match status). Seed prose printed the validator’s own target literal, causing self-match; metadata reworded, requested validator unchanged.

researcher-2-DONE-1
