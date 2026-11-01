# researcher-3 — C: automated block summaries / decompilation / verified evaluators

Question = what gets generated, what is proved once, what remains per function, costs + failure modes. Evidence = primary text + pinned source; upstream measurements attributed, not rerun. Every seeded row resolved; negative results = bounded searches, not nonexistence proofs.

**Decision input (inference): C is not an exclusive alternative to direct stepping or model refinement.** Named proof-producing block simplification, a verified reflective evaluator, and a full decompiler are different investments. All can support either route. Evidence below supports amortizing semantic plumbing, **not** a defensible LZ4 speedup, implementation-time forecast, or break-even point. FVA already has a verified stepper, contextual walker, access classifier and prefix-composition judgments; a second full Wasm interpreter is not the same unit as D9.

| id | question | answer | numbers | source (URL + verbatim excerpt) | applicability to FVA |
|---|---|---|---|---|---|
| R3.1 | What do HOL4 decompilation, AutoCorres, Leviathan and Picinae generate? Loops, certificate, remaining user work, tool cost? | HOL4 → tail-recursive function + conditional total-correctness certificate; user proves algorithmic property + generated precondition, including termination. AutoCorres → shallow monadic function + refinement to parsed C; loops remain a `whileLoop` combinator. Leviathan → C-like effects + equivalence theorem for loop-free blocks, with interactive branches/sharing. Picinae → address-indexed IL + reusable verified symbolic interpreter; user supplies cutpoint invariants/termination. These are distinct architectures, not interchangeable tools. | HOL4 original decompiler: 1,123 ML lines + ≈2,300 supporting proof lines, excluding ISA models. Picinae historical symbolic evaluator+correctness: ≈1,000 Coq lines. Leviathan rewrite library: ≈330 lemmas / ≈10,000 Isabelle lines, excluding parsers/case studies. | [HOL4 §II-D](https://www.cl.cam.ac.uk/~mom22/decomp.pdf): “implemented in 1123 lines of ML with approximately 2300 lines of supporting proof scripts”. [Picinae §3.2](https://personal.utdallas.edu/~hamlen/hamlen19feast.pdf): “the symbolic interpreter and its proof of correctness comprise about 1000 lines of Coq code”. [Leviathan §5.2](https://www.ssrg.ece.vt.edu/papers/cpp2019.pdf): “approximately 330 rewrite lemmas, constituting approximately 10000 lines of Isabelle code”. Artifact/certificate excerpts in R3.1 detail. | **Inference:** keep a generated block's concrete semantic certificate separate from its higher-level mathematical spec. Proof-producing generators need not be trusted; the certificate must refer to FVA's original semantics and actual linked module. Full function decompilation additionally needs control/result encoding, loop recursion, callee composition and memory abstraction. |
| R3.2 | Verified functional/big-step/reflective evaluators as proof tools; soundness once + reuse per function? | Clocked functional semantics expose equations and useful induction; fuel decreases only at nonstructural recursive calls. Reflection reifies symbolic inputs, runs a proved evaluator, and applies its soundness theorem. It does not mean running `decide` on every symbolic theorem. The evaluator's totality permits timeout; guest termination remains a proof. Picinae deliberately stops before unresolved branch/loop choices. | Owens et al. report CakeML's functional semantics across 12 ILs, ≈5,800 definition lines + ≈40,000 proof lines; **not evaluator-soundness-only or function-verification costs**. Wasm-specific soundness counts are separated in R3.3. No measured FVA-sized reflection advantage found. | [Owens et al. §§1,2.3,8](https://www.cse.chalmers.se/~myreen/esop16.pdf): “the ease of doing symbolic simulation in proofs via rewriting”; “the clock should only be decremented on recursive function calls for which the currently evaluated expressions does not decrease in size”; “12 intermediate languages (ILs), totaling ≈ 5,800 lines ... ≈ 40,000 lines of proof”. [Lean manual](https://lean-lang.org/doc/reference/4.35.0/Tactic-Proofs/Tactic-Reference/): `decide`: “The target is not allowed to contain local variables or metavariables”; `cbv`: “proofs ... only use the three standard axioms”. | **Inference:** use closed evaluation for fixed syntax/metadata and proof-producing symbolic reduction for open state. A reified evaluator needs a proved semantic interpretation, checked reification/certificate, and controlled unfolding. FVA's allowed axioms admit `cbv`; no `native_decide`/`bv_decide` needed. No tactic-performance experiment run here. |
| R3.3 | Wasm-specific certified decompiler or big-step evaluator for block/loop/br, labels, frames, calls; soundness vs small-step; size? | **Verified Wasm evaluators and relational big-step semantics exist; no certified Wasm→pure algorithm decompiler located in the named search.** Wasm Logic's relational big-step models normal/trap/break/return, equivalent to small-step on terminating runs. WasmRef-Isabelle and current WasmCert-Coq maintain label/frame stacks, with correctness against small-step. These are whole-language interpreters, not automatic function summaries. Talos's retained big-step evaluator is not counted as a confirmed general small-step-equivalent proof tool; detail explains the misleading regression names. | POPL'25 Table 2: baseline interpreter 456 LOC + soundness 1,084; optimized progressful implementation with embedded soundness/progressfulness 1,940 + trivial progress 37; Wasm2 version 2,463 + 37. Shared inversion/tactics/preservation excluded. WasmRef ≈5,500 implementation+verification LOC combined. Wasm Logic ≈10,400 added mechanization LOC, **not big-step-equivalence proof alone**. | [POPL'25 §4.2 Table 2](https://dl.acm.org/doi/10.1145/3704858#T2): `Interpreter 456 ... 1940 ... 2463`; `Interpreter Soundness 1084 ... Embedded`; `Progress ... 37 (trivial)`; “Auxiliary proofs and definitions ... are omitted ... required for all the approaches.” [WasmRef §1](https://ris.utwente.nl/ws/portalfiles/portal/359117826/3591224.pdf): “implementation and verification ... ∼5500 new lines of code.” [Wasm Logic §§1,2.4](https://www.cl.cam.ac.uk/~nk480/wasm-pl.pdf): “~10,400 lines”; “equivalent results for all terminating programs”. | **Inference:** these establish plausible reusable infrastructure, not its marginal value over FVA's existing verified stepper. Context-stack optimization is a candidate only if FVA profiling identifies context traversal. Preserve original semantics, nondeterministic coverage, `Must` and per-prefix accesses; runtime interpreter soundness alone is weaker. |
| R3.4 | How summaries carry every-step footprints + total correctness, not final-state frame alone? | Accumulate an access trace/predicate with semantic coverage, compose by conjunction/trace append, and include callees. Picinae infers accessibility from successful execution; that theorem alone is weaker than all-prefix safety. FVA already has the right split: prefix `Until` for a block/loop, `MustW` for the full continuation. An isolated block cannot certify all future accesses. Termination needs an input-dependent induction/rank or sufficient-fuel theorem. | No general extra-proof-cost ratio found. Reuse existing FVA judgments instead of adding a second footprint vocabulary. | [Picinae source:70–77](https://github.com/CharlesAverill/Picinae/blob/a87fc67dd1bafd4eccb35812f6459f51e4d79e3b/Picinae_finterp.v#L70-L77): “accumulates memory access predicates as a separate list”; “infer memory accessibility facts from successful executions”. [s2n safety:183–186](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/common/safety.ml#L183-L186): `memaccess_inbounds (APPEND e1 e2) rr wr <=> memaccess_inbounds e1 rr wr /\ memaccess_inbounds e2 rr wr`. FVA `FVA/Proof/Lib/Footprint.lean:7–12`: “a finite checked prefix alone never proves `Throughout`”. | **Inference:** generated summary → `Until H (Within R W) Exit c` under discharged obligations, with exact exit relation; compose by `Until.trans`, then `mustW_of_until` with the continuation. Whole call → `MustW`. Keep successful-access semantics, traps and termination distinct. Final-memory equality cannot rule out a read or a write later restored. |
| R3.5 | Measured build-tool vs prove-function effort; reuse and recompilation? | Tool LOC and translation/check CPU costs are sometimes separated from user proof size; author-hours rarely are. AutoCorres gives both translation cost and a strengthened user proof, while Picinae gives one expert's tiny-routine time. These do not establish a common effort ratio. **None found:** matched FVA-like break-even, per-release re-proof cost, or a comparable same-function direct/reflection/decompilation experiment. | AutoCorres Schorr–Waite: 19 C LOC → 57 pretty-printed model lines; abstraction 15.1 CPU s; user proof 807 lines incl. 160 termination. Picinae x86 strcmp: 15 instructions, ≈15 definition + ≈50 proof lines, ≈20 proof lines reusable boilerplate; expert ≈1 h. Different semantics, tools, contracts and eras. | [Greenaway thesis Tables 8.1–8.3](https://trustworthy.systems/publications/nicta_full_text/8758.pdf): `Schorr-Waite 19 1 120 57 766 311`; `Schorr-Waite 19 1 3.8 s 15.1 s 2.23 G`; `Termination 160`; `Total 807 577 3317`. [Picinae §4.3](https://personal.utdallas.edu/~hamlen/hamlen19feast.pdf): “Its 15 instructions implement a single loop”; “about 15 lines of definitions ... about 50 lines of proof”; “About 20 ... boilerplate”; “completed by an expert user in about 1 hour”. | **Inference:** account separately for one-time semantic/compiler tooling, per-artifact extraction/certificate replay, and per-function algorithm/invariant/memory proofs. Recompilation may preserve a model proof but still changes the artifact certificate. No sourced promise that this saves time for the decoder. |
| R3.6 | Term growth, readability, path explosion, calls/loops, memory aliasing; mitigations? | Stop reflection at unresolved control and split/induct; shield symbolic operators from evaluator unfolding; share subexpressions; use named join/cutpoint summaries; preserve access/address facts. A verified fast runtime interpreter is not automatically a fast symbolic prover. Calls, aliasing and overlapping copies remain semantic obligations. State joining may recover lifting scalability while sacrificing the information needed for functional correctness. | Picinae historical ARM memset: 31 instructions, 3 loops, ≈700 proof lines, ≈500 arithmetic. MirrorShard's reported reification bottleneck ≈50% of verification time. These are source-reported examples, not FVA forecasts. | [Picinae §4.2](https://personal.utdallas.edu/~hamlen/hamlen19feast.pdf): “three loops ... composing 31 instructions total”; “about 700 lines ... about 500 ... bit arithmetic”. [Pinned evaluator:474–483](https://github.com/CharlesAverill/Picinae/blob/a87fc67dd1bafd4eccb35812f6459f51e4d79e3b/Picinae_finterp.v#L474-L483): “stop interpretation early if it encounters a conditional or loop”; avoids “every possible branch ... fully expanded”. [MirrorShard §5.3](https://arxiv.org/pdf/1305.6543): “reification was a major performance bottleneck (taking almost 50% of total verification time)”. | **Inference:** keep block certificates small at both statement and proof-term levels; measure elaboration and independent kernel replay, not just tactic execution. Treat helper summaries and overlap-sensitive memory lemmas as first-class. A full evaluator rewrite needs an actual FVA measurement, not a runtime speedup borrowed from WasmRef. |
| R3.7 | Fresh Lean-native decompilation precedent beyond prior survey? | `dhsorens/riscv-decomp` implements `Cert = fn + pre + sound`, conditional-termination loop rules, and proved extraction for register-only loop bodies. `emitBody_sound` assumes `RunsTo` of the extracted body; user proves that by algorithmic induction. Memory/calls/nested loops are excluded from automatic extraction, even though hand-composed memory leaf rules exist. No-fuel public wording does not mean termination is free. | Local pinned text counts: body extractor 425 lines; extraction certificate 456; sum-down example 201. Example is four instructions. Counts exclude imported machine/logic libraries. No elapsed build/author-effort measurement found or run. | [README](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/README.md): “Refuses memory, calls, syscalls and nested loops.” [Certificate:46–64](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Certificate.lean#L46-L64): `pre : α → Prop`; `sound : ∀ x, pre x → cpsTotal ... (post (fn x))`. [Extract/Cert:389–395](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/Cert.lean#L389-L395): `(h : RunsTo body ... n x y) : cpsTotal ...`. Reproducible counts in detail. | **Inference:** concrete Lean design reference for certificate output + indexed termination, not ready Wasm support. README licence: “None yet — ask before depending on this.” No code adoption advised. Three-axiom claim is source-reported, not rebuilt/replayed/audited here. |
| R3.8 | Newer large-scale certified lifting: what does scale actually demonstrate? | Verbeek et al. PLDI'22 generate Hoare graphs: recovered instructions/control flow + inductive predicates + assumptions/proof obligations. This is scalable conditional lifting/sanity-property verification, **not** decompilation to an algorithm already proved functionally correct. Large extraction and the Isabelle-certified subset are separate results. | Xen extraction: 399,771 instructions; separately, exported CoreUtils subset: 16,078 instructions with all listed Hoare triples automatically proved. Neither number is a verified decoder/whole-Xen functional-correctness count. | [PLDI'22 §§5.1–5.2 Table 2](https://www.ssrg.ece.vt.edu/papers/pldi22.pdf): “399 771 instructions were lifted”; “For several CoreUtils binaries ... exported ... to ... Isabelle/HOL”; “Without exception, all Hoare triples could be proven automatically”; `Total 16 078 37`. Abstract: “If our technique succeeds and the proofs obligations are proven true, then ... under the generated assumptions ... correct.” | **Inference:** useful precedent for untrusted invariant/certificate generation, state joining and parallel proof obligations. For FVA, generated assumptions are obligations to discharge, not permission to shrink the all-input contract. Wasm's explicit control structure removes much x86 disassembly work; it does not automatically solve memory/algorithm invariants. |

## R3.1 — generated artifact, certificate, user obligation

### HOL4: function + generated precondition + total triple

Source: [Myreen–Gordon–Slind, original decompilation paper, §§II–IV](https://www.cl.cam.ac.uk/~mom22/decomp.pdf).

> “the decompiler derives a tail-recursive function and proves a theorem stating that the function accurately describes the effect of the given machine code”
>
> “the user can concentrate on proving properties of the generated function”
>
> “The precondition fpre ... states the side-conditions which must hold for f to execute properly.”

The generated certificate relates resource assertions/PC and code to the extracted function, conditional on `fpre`. It is **total correctness**, not a rewrite of source into a separately trusted program. §III-B:

> “Thus {p} c {q} is a total-correctness specification.”

Loops use `tailrec(x) = if G(x) then tailrec(F(x)) else D(x)`. §III-C:

> “tailrec can be defined directly (without a termination proof in HOL4)”
>
> “However, the decompiler requires tailrec to terminate for certain inputs.”

Its generated precondition combines eventual loop exit with side conditions at intermediate calls; the user discharges it. The linked-list example proves both length correctness and `fpre` by induction on the represented list. This is where mathematical input structure enters; automatic extraction alone is not the all-input result.

**Tool build size, not elapsed effort:** §II-D:

> “Our decompiler is currently implemented in 1123 lines of ML with approximately 2300 lines of supporting proof scripts, and works on top of models of x86, ARM and PowerPC whose HOL4 definitions total more than 10000 lines.”

The prior survey already records composition timings + tiny cross-architecture reuse. Those are not repeated as a new direct-vs-refinement result. New evidence here = generator/support size and exact division of user obligations. HOL4's unrestricted tail-recursion encoding is not directly Lean total recursion; R3.7 supplies one Lean conditional-termination encoding.

### AutoCorres: proof-producing semantic abstraction, not binary extraction

Sources: [PLDI'14 §§1–2](https://trustworthy.systems/publications/nicta_full_text/7629.pdf), [project](https://trustworthy.systems/projects/OLD/autocorres).

> “automatically abstracts low-level C semantics into a monadic shallow embedding ... and produces a proof that it did so correctly”
>
> “AutoCorres presents to the end user a representation of the program that is simpler to reason about, while additionally producing a proof that the original program is a formal refinement of the final representation.”
>
> “loops are represented by the combinator whileLoop c B i with loop condition c, body B, and initial loop iterator value i.”

The pipeline includes deep→shallow conversion, local-variable lifting, word/heap abstraction, simplification and type specialization. The source parser remains trusted. PLDI'14:

> “the parser is a trusted piece of the verification chain”
>
> “calls to function pointers” [among then-unsupported constructs].

Historical subset limits are attributed to that paper, not asserted about current AutoCorres2. Inference: FVA can copy the **architectural idea** of proof-producing abstraction without importing that source-parser trust boundary or rewriting source. Integer abstraction needs overflow guards/discharges; heap abstractions need suitable validity/type conditions. Byte-oriented/overlapping LZ4 memory may demand retaining the low-level memory view.

The user still proves the output's specification. PLDI'14's list reversal figure includes a `guard` before dereference and a `whileLoop`; the text explains that extending the represented-list invariant with pointer validity discharges those guards. A higher-level model reduces plumbing but does not erase the actual memory preconditions.

### Leviathan: interactive symbolic block abstraction

Source: [CPP'19 §§1,5,7](https://www.ssrg.ece.vt.edu/papers/cpp2019.pdf).

> “a block is defined as a sequence of instructions that can be modeled with only if-then-else statements (no loops)”
>
> “The starting point is ... run(σb) = ?f(σb) ... It is a schematic variable.”
>
> “Whenever two subgoals are introduced, an if-then-else is introduced in the logic manually.”

The proof-producing simplifier discovers `f` while establishing its equivalence to instruction execution. Users may select a branch by a precondition instead of retaining a conditional. This is a contract decision: an assumption that excludes a legal decoder path cannot silently become part of an all-input theorem.

Tool support, §5.2:

> “the library consists of approximately 330 rewrite lemmas, constituting approximately 10000 lines of Isabelle code. This excludes the case studies and the parsers.”

Readability is not fully automatic, §7:

> “There are two types of user interaction required. The first concerns the introduction of if-then-else statements. The second interaction is introducing let-constructs.”
>
> “without this interaction the extracted semantics can become significantly larger and more unreadable.”

Inference: generated exact state expressions are useful intermediate certificates; a proof-friendly algorithmic abstraction is an additional product. Keep that difference when estimating what block summaries buy.

### Picinae: lifted IL + proved symbolic evaluation + invariants

Source: [FEAST'19 §§2–3](https://personal.utdallas.edu/~hamlen/hamlen19feast.pdf).

> “Raw native code is first lifted to an IL data structure expressed as a .v file”
>
> “Lifted code is formalized in Coq as a partial function from addresses a to pairs (sz, q)”
>
> “The symbolic interpreter elaborates these core definitions to build a more efficient transition system for the IL”

It does not recover a pure recursive algorithm and declare it correct. Its user-facing invariant schema starts symbolic evaluation at each cutpoint and asks for preservation/exit; total correctness additionally asserts a finite terminating execution. Historical sizes, §§3.1–3.4:

> “core definitions ... about 200 lines of Coq code”
>
> “symbolic interpreter and its proof of correctness comprise about 1000 lines”
>
> “proof library ... about 3,500 lines”
>
> ISA tactic libraries “about 550 and 500 (respectively) lines” [Intel x86 / ARM32].

These are separately scoped components, not an independent estimate of implementation time. The BAP lifting connection is not established by the symbolic evaluator's theorem alone. FVA should retain its existing byte-checked lift + original semantic relation rather than inherit an unproved lifter boundary.

## R3.2 — functional semantics, reflection, reuse

### Clocks support proof by rewriting; they do not prove guest termination

Source: [Owens–Myreen–Kumar–Tan, ESOP'16 §§1,2.3,7–8](https://www.cse.chalmers.se/~myreen/esop16.pdf).

> “A functional big-step semantics is essentially an interpreter written in a purely functional style and equipped with a clock to ensure that the function is total, even when run on diverging programs.”
>
> “the clock should only be decremented on recursive function calls for which the currently evaluated expressions does not decrease in size.”

The proof's well-founded measure combines clock and syntax size. Divergence/termination are properties obtained by quantifying over clocks, not by treating the evaluator's termination as the program's. Correspondence to small-step explicitly constructs an execution trace:

> “we represent the small-step trace with a list so that we can check its length”
>
> “The length check ensures that if the functional big-step diverges, then we will be able to build a small-step trace of arbitrary length”

§8 reports:

> “12 intermediate languages (ILs), totaling ≈ 5,800 lines. There are about ≈ 40,000 lines of proof about them.”

That aggregate includes substantial compiler verification. It is not a soundness-proof count for a small block evaluator and does not estimate a new FVA implementation.

Nondeterminism needs care. The paper supports oracles and separately relates oracle semantics to a nondeterministic LTS. For FVA's deterministic integer decoder subset, a unique-step certificate can simplify the argument; a generic evaluator must still cover permitted semantic choices. One successful run is not a demonic/all-executions theorem without such a justification.

### Reflection amortizes a proved procedure; engineering still matters

Source: [MirrorShard §§1,4–5](https://arxiv.org/pdf/1305.6543).

> “instead of writing a procedure that generates a proof on each invocation, we instead verify the procedure itself”
>
> “Memory Evaluators are verified functions that reason about reads from and writes to heaps satisfying a separation logic assertion.”

Its proof-side evaluator interprets reified syntax under verified hints and representation predicates; users still supply invariants/hints for their abstract data structures. It is not unrestricted computation over arbitrary symbolic Lean state.

Source: [pinned Picinae `Picinae_finterp.v:42–50`](https://github.com/CharlesAverill/Picinae/blob/a87fc67dd1bafd4eccb35812f6459f51e4d79e3b/Picinae_finterp.v#L42-L50):

> “The interpreter is proved correct according to the operational semantics, so it does not contribute to Picinae's trusted core definitions.”

The actual theorem [`reduce_stmt'`:1076–1087](https://github.com/CharlesAverill/Picinae/blob/a87fc67dd1bafd4eccb35812f6459f51e4d79e3b/Picinae_finterp.v#L1076-L1087) assumes `exec_stmt ...`, then returns existential unknown choices, final-state correspondence or a residual continuation, plus `conjallT ma`. The proof proceeds by induction on statement syntax. Its signature's direction matters: it transforms a successful execution hypothesis; it does not independently establish termination/memory safety for all starting states.

**Lean boundary:** [version-pinned manual](https://lean-lang.org/doc/reference/4.35.0/Tactic-Proofs/Tactic-Reference/):

> `decide`: “The target is not allowed to contain local variables or metavariables.”
>
> “decide +kernel uses kernel for reduction instead of the elaborator.”
>
> “cbv unfolds definitions using their equational lemmas ... producing propositional equality proofs at each step.”
>
> “The proofs produced by cbv only use the three standard axioms (propext, Quot.sound, and Classical.choice).”

Inference: `decide +kernel` is excellent for concrete emitted syntax/equalities/checks; universally quantified state behavior still needs semantic lemmas, reflection with a proved interpretation, or symbolic proof-producing simplification. `cbv` is axiom-compatible; this survey did not benchmark it on a decoder block.

## R3.3 — Wasm-specific state of the art

### Wasm Logic: relational big-step, explicit nonlocal control

Source: [ECOOP'19 §§2.4,5](https://www.cl.cam.ac.uk/~nk480/wasm-pl.pdf).

> “we define and mechanise ... a WebAssembly big-step semantics that we formally prove equivalent, up to transitive closure, to the mechanised small-step semantics”
>
> “Normal ... Trap ... Break i ... Return” [execution result constructors].
>
> “equivalent results for all terminating programs”

Break carries remaining label depth; return propagates to the function boundary. The judgment is parameterized by break-label arities and return arity. This is a useful structured-control representation precedent, **not an executable decompiler or a total-correctness theorem for every function**.

Whole addition size, §1:

> “~10,400 lines of non-comment, non-whitespace Isabelle code, not counting code inherited from the existing mechanisation.”

No isolated size of the big-step↔small-step proof confirmed in that paper. The prior survey's program-logic examples are not re-counted as block-summary benchmarks.

### WasmRef-Isabelle: verified optimized state/control interpreter

Source: [PLDI'23 §§1,4.1–4.3](https://ris.utwente.nl/ws/portalfiles/portal/359117826/3591224.pdf).

> “our implementation and verification of WasmRef-Isabelle comes to ∼5500 new lines of code.”
>
> “First, we define an intermediate interpreter which implements only control flow optimisations ... proven sound ... Second ... a monadic interpreter ... replace[s] ... lists ... with monadic arrays.”

The intermediate representation maintains stacks of labels and frames:

> “evaluation of block, loop, if, and function calls adding to these stacks instead of introducing a label or frame expression in the reduct”
>
> “identifying the jump target for a br becomes a matter of directly walking the label stack”

Its `run_iter_sound` theorem relates a fuelled iterator to the transitive closure of the original reduction relation. Its result relation allows successful values, trap, **or crash/fuel exhaustion**. The paper explicitly limits coverage of nondeterminism:

> “this interpreter can only be sound with respect to Wasm’s operational semantics, not complete.”

Inference: runtime soundness is reusable, but total function proofs must exclude the crash/timeout alternatives and justify all-execution coverage for the actual subset. Mutable-array runtime speedups do not directly establish faster kernel evaluation of open symbolic memory terms.

### WasmCert-Coq / Progressful Interpreters: direct soundness-size evidence

Sources: [POPL'25 §4.2 Table 2](https://dl.acm.org/doi/10.1145/3704858#T2), [artifact](https://zenodo.org/records/14052598), current pinned source `58a3d3f8b7af4dc8aa9351f254a9e672643b21f8`.

Verbatim relevant table entries (columns abbreviated, no new measurements):

| component | original WasmCert-Coq | optimized progressful | optimized progressful, Wasm 2.0 |
|---|---:|---:|---:|
| Interpreter | 456 | 1940 | 2463 |
| Interpreter Soundness | 1084 | Embedded | Embedded |
| Interpreter Progressfulness | Not Proved | Embedded | Embedded |
| Progress | 1039 | 37 (trivial) | 37 (trivial) |
| Total | 2579 | 1977 | 2500 |

Scope qualifier:

> “Auxiliary proofs and definitions, such as the typing inversion lemmas, automation tactics, and proofs to the preservation properties are omitted ... required for all the approaches.”

These are the strongest found **separated interpreter-soundness costs**. They do not count verified decompilation, invariant synthesis, function correctness, footprint propagation, or all required metatheory.

Pinned [`theories/interpreter_ctx.v:75–91`](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interpreter_ctx.v#L75-L91) returns a dependent `RSC_normal` with:

```coq
reduce_ctx hs hs' cfg cfg' ->
valid_ccs_cfg cfg' ->
run_step_ctx_result hs cfg depth
```

[`contexts.v:1097–1106`](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/contexts.v#L1097-L1106) defines `reduce_ctx` by conversion back to the original `reduce` relation, not a second unrelated semantics. Helpers explicitly implement [`run_ctx_br`, `run_ctx_return`, `run_ctx_invoke`:165–247](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interpreter_ctx.v#L165-L247).

[`interpreter_ctx.v:1943–1953`](https://github.com/WasmCert/WasmCert-Coq/blob/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8/theories/interpreter_ctx.v#L1943-L1953):

```coq
Fixpoint run_multi_step_ctx (fuel: nat) ... :=
  match fuel with
  | 0 => inl None
  | S n => ...
```

The current file is a one-step proof-carrying interpreter plus iterator, **not a syntax-directed evaluator that automatically emits an abstract algorithm per function**. Local count `wc -l theories/interpreter_ctx.v theories/contexts.v` at that SHA → `1964`, `1196`, `3160 total`; whole files include definitions/proofs/comments and import shared infrastructure. Do not confuse this current count with the paper's differently scoped table.

### Talos: retained big-step evaluator, no general bridge confirmed

Pinned source: `80644390de3ad4db3055445259a034413ae41577`.

[`interpreter/Interpreter/Wasm/Semantics.lean:465–481`](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/interpreter/Interpreter/Wasm/Semantics.lean#L465-L481):

> “Big-step fuel-bounded interpreter.”
>
> “execOne runs a single instruction ... exec runs a Program ... run runs a function call”

A current general big-step→authoritative-small-step correspondence was **not confirmed** in the inspected interpreter/codelib paths. Do not treat a theorem's name as evidence: [`Examples/SmallStep.lean:40–42`](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/interpreter/Interpreter/Wasm/Examples/SmallStep.lean#L40-L42) calls its theorem `arithmetic_matches_big_step`, but it compares to `runValues`. [`Examples/Harness.lean:7–9,30–37`](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/interpreter/Interpreter/Wasm/Examples/Harness.lean#L7-L9) explicitly states and implements:

> “These compatibility projections execute only the authoritative small-step runner; they do not call the retained big-step semantics.”

Search surfaces: `interpreter/Interpreter/Wasm/**`, `codelib/CodeLib/SepLogic/**`, filenames containing equivalence/refinement/bridge/soundness; inspected `Examples/SmallStep.lean`, `Examples/Harness.lean`, `CodeLib/Equivalence.lean`. The latter relates program entrypoints, not the two semantic styles. Positive control: exact `## Big-step fuel-bounded interpreter.` in `Semantics.lean` → expected `1`, rc 0. Search results include concrete regression theorem names; no claim of exhaustive theorem-name coverage or whole-repo proof audit.

### None found — certified Wasm→pure-function decompiler

Places searched: primary WasmCert-Coq repository + current README; WasmRef and Progressful papers; Wasm Logic paper; Talos interpreter/codelib; HOL4 and RISC-V decompilation sources; indexed scholarly/GitHub search. Query variants:

```text
WebAssembly decompilation into logic verified decompiler Coq Isabelle big step evaluator summary
"WebAssembly" "decompilation into logic"
"verified" "Wasm" "big-step" "interpreter" decompiler
WebAssembly verified decompiler "logic" "Lean" 2026
WebAssembly verified symbolic evaluator block summaries "sound"
"Wasm" "big-step" "Lean" evaluator
```

Later variants mostly resurfaced Wasm Logic, WasmRef, WasmCert, Talos, SpecTec, RISC-V decompilation, non-certified conventional Wasm decompilers, or the reverse direction Coq→Wasm compilation. No additional confirmed certified Wasm→algorithm extractor emerged. This is a bounded discovery search, not a systematic census or proof of absence.

## R3.4 — access coverage + totality in a compositional summary

**Primary executable-summary precedent:** pinned [Picinae evaluator:146–149](https://github.com/CharlesAverill/Picinae/blob/a87fc67dd1bafd4eccb35812f6459f51e4d79e3b/Picinae_finterp.v#L146-L149):

```coq
Definition MemAcc (P: store -> addr -> Prop) s a w len :=
  forall n, n < len -> P s ((a+n) mod 2^w).
```

The evaluator returns state expressions, a residual/exit continuation and `ma : list Prop`; sequence concatenates `ma1++ma2`. Its correctness theorem infers those propositions from successful original executions. This is useful but must not be mistaken for an unconditional proof that every legal initial state is safe/terminates.

**Primary trace-composition precedent:** pinned [s2n `common/safety.ml:183–186`](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/common/safety.ml#L183-L186):

```text
memaccess_inbounds (APPEND e1 e2) rr wr
  <=> memaccess_inbounds e1 rr wr /\ memaccess_inbounds e2 rr wr
```

Its event predicate checks separate read/write ranges including access widths. This adds the composition seam missing from merely listing final heap frame conditions.

**FVA already owns the target judgments** (local source, no edits):

- `/home/eturkes/Projects/fva/FVA/Spec/Exec/Access.lean:60–65`: `Within` quantifies `Reads` and `Writes`; `Throughout H P c := ∀ c', Steps H c c' → P c'`.
- `/home/eturkes/Projects/fva/FVA/Proof/Lib/Footprint.lean:21–28`:

  ```lean
  def MustW ... := Must H Q c ∧ Throughout H (Within R W) c
  inductive Until ... where
    | done ... : Q c → Until H P Q c
    | next ... : P c → (∃ c', Step H c c') →
        (∀ c', Step H c c' → Until H P Q c') → Until H P Q c
  ```

- Same file `:224–240`: `mustW_of_until` consumes `Until H (Within R W) X c` + `MustW` at every exit; `Until.trans` composes prefixes.
- Same file `:207–220`: unique computed steps transport `MustW`/`Until`; local footprints come first.

**Inference: minimal useful generated certificate** = under preconditions + emitted arithmetic/access obligations, establish `Until H (Within R W) Exit c`, where `Exit` pins a genuine control cutpoint and exact symbolic state relation. For a loop, induction proves repeated summary composition reaches an exit. For a call, use the callee's full contract and propagate its accesses. Then combine with the continuation via `mustW_of_until`. This preserves every prefix while avoiding any claim about code beyond the block's exit.

Termination obligations remain visible: mathematical induction on remaining input/work, a well-founded measure, or an existence/sufficient-fuel theorem. Invalid/error-return paths belong in the same coverage. FVA's `Reads`/`Writes` deliberately omit trapping accesses (`Access.lean:8–11`), so successful-access bounds, absence of traps and specified error behavior are distinct properties. No footprint-only theorem should be advertised as a complete memory-error/termination proof.

## R3.5 — effort accounting and reuse limits

### AutoCorres: one-off abstraction and user correctness proof separated

Source: [Greenaway thesis, Tables 8.1–8.3 / pp.167,173–174](https://trustworthy.systems/publications/nicta_full_text/8758.pdf).

Verbatim table rows:

```text
Table 8.1 (This Work):
List definitions 64
Partial correctness 528
Fault freedom 44
Termination 160
Miscellaneous 11
Total 807

Table 8.2:
Schorr-Waite  19  1  120  57  766  311
seL4 kernel  10 121  551  20 576  11 928  318  112

Table 8.3:
Schorr-Waite  19  1  3.8 s  15.1 s  2.23 G
seL4 kernel  10 121  551  39.2 min  70.1 min  5.59 G
```

Column meanings: C LOC / functions; parser vs AutoCorres pretty-printed model lines and average term size; parser vs AutoCorres **CPU time**, with joint peak memory. Hardware/count qualifier:

> “16-core 3.3GHz Intel Xeon E5-2643, with 128GiB of RAM ... average of 5 runs.”

These are **not wall-clock author time**. Translation output can be saved and reused:

> “for both tools this cost tends to be a one-off, where the results of the translation are saved and reused.”

Proof reuse/remaining obligation:

> “we required total correctness ... requiring around 160 lines of new proof script.”
>
> “the main body of the proof shared 335 lines (66%).”

The source algorithm proof already existed; the new proof added validity/termination and adapted framework syntax. This is evidence of reuse under controlled abstractions, not a general direct-vs-decompilation effort ratio. The seL4 rows are **abstraction scalability**, not full functional proofs delivered by AutoCorres automatically.

### Picinae: per-routine math remains after shared evaluator

Source: [FEAST'19 §§4.1–4.3](https://personal.utdallas.edu/~hamlen/hamlen19feast.pdf).

| routine | source-reported artifact/effort | verbatim excerpt |
|---|---|---|
| ARM strlen | ≈230 total proof lines, ≈80 computational | “total correctness ... about 230 lines”; “only about 80 lines regard the computational aspects”. |
| ARM memset | 31 instructions / 3 loops; ≈700 proof lines, ≈500 arithmetic | “three loops ... 31 instructions total”; “about 700 lines, of which about 500 are devoted to bit arithmetic properties”. |
| x86 strcmp | 15 instructions; ≈15 definition + ≈50 proof lines; ≈20 boilerplate; expert ≈1 h | “15 instructions”; “15 lines of definitions ... 50 lines of proof”; “20 ... boilerplate”; “expert user in about 1 hour”. |

Scope is tiny optimized library routines with a mature shared proof framework, not the decoder. Numbers are not locally reproduced author-time measurements.

### None found — actionable break-even / release-maintenance ratio

Searched HOL4 original + improved-decompilation project/papers, AutoCorres paper/thesis evaluation, Leviathan paper, Picinae paper/current code, WasmRef/Progressful paper effort sections, current Lean decompiler README/examples. Search phrasings included:

```text
"decompilation into logic" "build" "effort" "tool"
"AutoCorres" "development" "years" "lines"
"decompilation into logic" "proof effort" comparison direct
"machine-code verification" "compiler versions" proof reuse
"Wasm" "verified evaluator" "proof size"
```

No matched experiment isolated building a symbolic evaluator versus using it across FVA-comparable functions, no per-release maintenance ledger, and no defensible break-even number. Do not replace those missing measurements with tool LOC or extraction throughput. Whole-language evaluator size overstates the marginal cost if FVA reuses its current verified machinery, but the amount is unmeasured.

**Inference: accounting for an FVA comparison** = build-once soundness/generator work + extraction/certificate construction per changed artifact + algorithm/model/invariant proofs + access/termination proofs + elaboration/kernel replay/resources. Keep generated source size and human-reviewable spec size separate: proof-side scaffolding need not enter the reviewed spec, provided the final theorem still concerns the linked original semantics.

## R3.6 — failure modes and remedies with evidence

| failure | primary excerpt | consequence for FVA (inference) |
|---|---|---|
| Blind reflective reduction destroys abstraction | [Picinae `finterp.v:152–159`](https://github.com/CharlesAverill/Picinae/blob/a87fc67dd1bafd4eccb35812f6459f51e4d79e3b/Picinae_finterp.v#L152-L159): `vm_compute`/`native_compute` perform “uncontrolled expansion of every term, resulting in huge terms ... intractable ... very slow for Coq”. | Shield symbolic arithmetic/memory operations; compute syntax/control plumbing only; restore operators through checked equalities. Do not unfold the whole state to obtain one segment effect. |
| Symbolic branch/loop explosion | [same:474–483](https://github.com/CharlesAverill/Picinae/blob/a87fc67dd1bafd4eccb35812f6459f51e4d79e3b/Picinae_finterp.v#L474-L483): residual continuation permits stopping “early ... conditional or loop ... case-distinction or induction”. | Summarizer returns control exits/residual goals; induction handles unbounded iteration. Avoid evaluating every path into one giant conditional. |
| Repeated subterm expansion/readability | [Leviathan §7](https://www.ssrg.ece.vt.edu/papers/cpp2019.pdf): “Whenever a value occurs twice ... determined manually whether ... introduce a let”. | Introduce named intermediate values/shared DAGs and exact segment theorems; reduce once at joins. Preserve address/range expressions needed for footprint obligations. |
| Small tactic time, large replay time | [MirrorShard §5.4](https://arxiv.org/pdf/1305.6543): “proof terms that take substantially longer to check than the proof script took to run”; partially reduced terms “requiring them to be reduced multiple times during subsequent proof checking”. | Profile elaboration and kernel checking separately; cache meaningful certificate lemmas, not only tactic script chunks. |
| Reification becomes the bottleneck | [MirrorShard §5.3](https://arxiv.org/pdf/1305.6543): “almost 50% of total verification time”. | A proved symbolic evaluator is not automatically economical; account for reification/expression sharing too. |
| Runtime control representation imposes traversal cost | [WasmRef §4.2](https://ris.utwente.nl/ws/portalfiles/portal/359117826/3591224.pdf): naïve interpreter “re-derive[s] the shape of the evaluation context in linear time with each step”. | Consider context-stack/block-evaluator refactoring only after observing the cost in FVA. A change to proof-side representation can retain original `Step` through a theorem. |
| Arithmetic dominates after stepping is automated | [Picinae §4.2](https://personal.utdallas.edu/~hamlen/hamlen19feast.pdf): “bulk ... complexity is dominated by ... obscure numerical properties of bit arithmetic”. | Copy bounds, modular arithmetic and overlapping-copy semantics can dominate even after block extraction succeeds. |
| Aliasing can invalidate simplification | [Leviathan §5.2](https://www.ssrg.ece.vt.edu/papers/cpp2019.pdf): disjoint read/write rule requires separation; “Without the assumption, the write may overwrite some of the bytes ... invalidating the lemma.” | Derive valid separation per actual stripe/helper, or use overlap-aware memory lemmas. Never assume global disjointness merely to make generated expressions simpler. |

FVA-specific synthesis: helper calls are summary seams, not instructions to inline repeatedly. A callee summary should state its true precondition, exact/abstract memory effect, all internal access bounds and termination. The caller proves that precondition at each site. LZ4's sequential overlapping matches require a recurrence over evolving output, not snapshot-copy substitution. These are semantic deductions from the contract + memory operations; no new performance claim is made.

## R3.7 — Lean decompilation artifact, constraints, measured source scope

Pin: [`dhsorens/riscv-decomp@0261343853e3a4e1ca189255c17092ff3eb81942`](https://github.com/dhsorens/riscv-decomp/tree/0261343853e3a4e1ca189255c17092ff3eb81942).

[`Decomp/Certificate.lean:46–64`](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Certificate.lean#L46-L64): `Cert` carries `entry`, `exit_`, code requirement, `fn`, `pre`, input/output couplings and:

```lean
sound : ∀ x, pre x → cpsTotal st entry exit_ cr (couple x) (post (fn x))
```

[`Decomp/Triple.lean:78–82`](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Triple.lean#L78-L82) defines `cpsTotal` with an existential finite `st.iter` execution and preserved frame. It is not an FVA access theorem.

[`Tailrec.lean:124–136`](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Tailrec.lean#L124-L136) uses an iteration-indexed inductive `TerminatesIn`; `Terminates` existentially quantifies the index. This avoids eliminating a general proof from `Prop` into a computed trip count. It does **not** avoid proving termination: it packages termination + side conditions for induction.

[`Extract/Cert.lean:389–395`](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/Cert.lean#L389-L395) is universally quantified over emitted bodies but still assumes:

```lean
(hbody : emitBody bs info = some body)
(hpass : passOk cr rs ... = true) (hj : jumpsOk cr bs = true)
(h : RunsTo body (fun _ => True) n x y)
```

So a reusable theorem buys the body→machine link, not the mathematical `RunsTo` proof. [`Extract/SumDown.lean:13–26`](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/SumDown.lean#L13-L26) makes the user work explicit:

> “two equations read off it ... then an ordinary induction on the counter”
>
> “The two equations are still written by hand from the emitted function”

The actual [`sd_runsTo`:174–190](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/SumDown.lean#L174-L190) proves a run for each representable counter; `sumDown_correct` composes it with the extraction certificate.

**Scope exclusions**, [`Extract/Body.lean:35–44`](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/Body.lean#L35-L44):

> “Registers only ... Loads, stores, ECALL, EBREAK, JALR, a JAL that writes a register (a call) ... are out”
>
> “One loop, no nesting.”

Important correctness/usefulness distinction, same file `:23–31`: unsupported fallback can produce a sound zero-step exit **inside** the loop; the source explicitly says proving static checks exclude that fallback is not done. A consumer must prove the intended exit/result, not equate sound extraction with useful whole-loop progress.

**Local source measurement** (no source execution):

```text
wc -l Decomp/Extract/{Body,Cert,SumDown}.lean
425 .../Body.lean
456 .../Cert.lean
201 .../SumDown.lean
```

Pinned raw files make those counts reproducible. Counts include comments/blanks; they exclude imported machine semantics, separation logic, loop infrastructure and other libraries. The four instructions are explicitly listed at [`SumDown.lean:40–45`](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/SumDown.lean#L40-L45).

**Replay caveat**, same file `:130–131`:

> “one simp only over both blocks hands the kernel a term it cannot check (deep recursion); block by block it is immediate.”

Source-reported, not rerun. [`README:133–138`](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/README.md#L133-L138) claims the allowed three axioms; this task did not execute its checks or audit the whole import closure. [`README:177–179`](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/README.md#L177-L179):

> “Licence ... None yet — ask before depending on this.”

Inference: useful design precedent, not an Apache-compatible dependency/adoption recommendation or evidence that optimized memory-heavy Wasm decompilation is already cheap.

## R3.8 — larger lifting results are not algorithmic correctness results

Source: [Verbeek–Bockenek–Fu–Ravindran, PLDI'22 §§1,5–8](https://www.ssrg.ece.vt.edu/papers/pldi22.pdf).

The generated artifact is a Hoare graph: instructions/control flow with one-step inductive predicates, memory relations and explicit assumptions. It can be exported to Isabelle. Conditional claim:

> “If our technique succeeds and the proofs obligations are proven true, then ... under the generated assumptions ... the lifted representation is correct.”

Separate scales:

- §5.1: “399 771 instructions were lifted” across Xen binaries/library functions.
- §5.2: “For several CoreUtils binaries ... exported ... to ... Isabelle/HOL”; “Without exception, all Hoare triples could be proven automatically.” Table 2: `Total 16 078 37` (instructions / resolved indirections).

The large Xen extraction is **not** the same as the Isabelle-replayed subset, much less a full functional-correctness proof of Xen or GCC. The paper is also distinct from FoxDec's C-code decompilation, which its related work lists separately.

Joining prevents repeated-path explosion but can discard useful function semantics. §1:

> “do not accurately model partial overlap, but instead simply destroy all regions in memory that may partially overlap”

External calls incur explicit assumptions. §5.3's overflowing `memset` example:

> “the algorithm asserted and noted as proof obligation that the write executed by memset did not exceed 32 bytes.”

It did not automatically verify the missing callee behavior. Inference for FVA: invariant proposals/callee assumptions must be discharged against the exact all-input contract. Preserving merely enough information for control-flow integrity is not enough for decoding correctness or per-step buffer bounds.

## Evidence + validation boundary

- Read primary PDFs via `webtext`/`pdftotext`; visually inspected relevant PDF pages, including tables/formulas. ACM Progressful full text read in owned BrowserOS Neo tab; old author PDF URL returned HTTP 404, direct ACM PDF returned HTTP 403, but full article/table text was available through the browser. No access-gate workaround or account change.
- Pinned repositories: WasmCert-Coq `58a3d3f8b7af4dc8aa9351f254a9e672643b21f8`; Picinae `a87fc67dd1bafd4eccb35812f6459f51e4d79e3b`; riscv-decomp `0261343853e3a4e1ca189255c17092ff3eb81942`; Talos `80644390de3ad4db3055445259a034413ae41577`; s2n single pinned source `573ea98f6a2eea3172f6146f83b86b9e526ce2dd`. Shallow source snapshots / selected files, not history/fork audits.
- Local measurements = source line counts + quoted positive-control match. Source-reported elapsed times/LOC remain attributed. No Lean/Coq/HOL/Isabelle builds, FVA gates, runtime proof benchmarks, independent kernel replays, or new correctness proofs ran. No claim that any upstream whole trust closure was verified here.
- Deliverable validation (`grep -c` unfilled-cell test + row count + structural parser): positive control expected `1` → `1`, rc `0`; actual unfilled cells expected `0` → `0`, rc `1` (grep's no-match status); target rows expected `8` → `8`, rc `0`; parser output `table_rows=8 columns=6 details=8`, rc `0`. Validator self-match removed; checks themselves unchanged.
- Search is bounded by indexing + named surfaces. None-found cells record what was searched; no numerical prediction or absence proof replaces the missing evidence.
- Temporary clones/downloads and the browser's task-generated text capture are removed at close. Useful owned source tabs remain open.
- Seed validator flaw repaired in this allowed file only: the preamble originally contained the exact unfilled-cell grep literal and therefore matched itself. The requested validator command remains unchanged externally; this report now omits that literal.

## Sources

- [HOL4 decompilation](https://www.cl.cam.ac.uk/~mom22/decomp.pdf)
- [AutoCorres PLDI paper](https://trustworthy.systems/publications/nicta_full_text/7629.pdf) · [thesis](https://trustworthy.systems/publications/nicta_full_text/8758.pdf)
- [Leviathan](https://www.ssrg.ece.vt.edu/papers/cpp2019.pdf) · [Picinae](https://personal.utdallas.edu/~hamlen/hamlen19feast.pdf)
- [Functional Big-Step Semantics](https://www.cse.chalmers.se/~myreen/esop16.pdf) · [MirrorShard](https://arxiv.org/pdf/1305.6543)
- [Wasm Logic](https://www.cl.cam.ac.uk/~nk480/wasm-pl.pdf) · [WasmRef-Isabelle](https://ris.utwente.nl/ws/portalfiles/portal/359117826/3591224.pdf) · [Progressful Interpreters](https://dl.acm.org/doi/10.1145/3704858)
- [WasmCert-Coq source](https://github.com/WasmCert/WasmCert-Coq/tree/58a3d3f8b7af4dc8aa9351f254a9e672643b21f8) · [Lean decompiler source](https://github.com/dhsorens/riscv-decomp/tree/0261343853e3a4e1ca189255c17092ff3eb81942)
- [Certified lifting PLDI'22](https://www.ssrg.ece.vt.edu/papers/pldi22.pdf) · [Lean tactic reference](https://lean-lang.org/doc/reference/4.35.0/Tactic-Proofs/Tactic-Reference/)

researcher-3-DONE-1
