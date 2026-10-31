# researcher-1 — loop proofs over machine code: methods + measured scale

| id | question | answer (method, project, how) | numbers (instr/function, proof size, check time) | source (URL + verbatim excerpt) | applicability to a Wasm stack machine in Lean |
|---|---|---|---|---|---|
| A1 | Methods for all-input proofs of loops in machine-code semantics: inductive assertions at cutpoints, symbolic execution + invariants, decompilation into logic, simulation/refinement to a functional model — which projects use which | **Direct:** s2n-bignum = symbolic blocks + loop invariants; TACAS memory-usage certificates = generated invariants + compositional Hoare rules. **Extract/refine:** HOL4 = instruction theorems → recursive model + certificate; seL4 = C/binary graphs + induction at paired cutpoints; CompCert = state simulation per compiler pass. These are composable techniques, not mutually exclusive stacks. | Functional proof scale: s2n inverse 1,033 instructions; decompilation scale: HOL4 Skein 1,352 instructions; seL4 whole-binary scale 11,736 instructions. These measure different artifacts/obligations; see A2–A4. | [HOL4 §III](https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf): “If the code has a loop, a loop rule is applied which wraps the result up using a tailrec-combinator and combines the resulting side condition on termination with the other side conditions.” [seL4 §3.3.5](https://www.cl.cam.ac.uk/~mom22/pldi13.pdf): “The rule names a C split point c_sp, a binary split point b_sp, an equality predicate P and a bound n.” [s2n proof](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/arm/proofs/bignum_copy.ml#L107-L117): `ENSURES_WHILE_UP_TAC` / `bignum_from_memory(z,i) s = lowdigits a i`. More source excerpts below. | **Inference:** both spike routes have precedents. Share instruction/block-effect lemmas; compare invariant composition with recursive-model simulation on the same loop. A proof of the model alone is insufficient; a final-state simulation alone is insufficient for the per-step footprint. |
| A2 | Decompilation into logic (Myreen, Gordon, Slind; HOL4/CakeML): machine code → functional model + certificate theorem; how loops become recursive functions; automation level | HOL4 automatically evaluates instruction semantics, builds a CFG, isolates nested loops into rounds, composes basic effects, turns backedges into tail recursion, and proves a certificate relating the extracted function to ISA semantics. Extracted `cond` includes validity + termination obligations; the verifier must prove it true. Original CakeML used decompilation to verify bytecode→x86-64 blocks; the later multi-target compiler uses a verified assembly IL instead. | Fig. 1: array sum 4 instructions, old/new composition 2.5/0.3 s; copying GC 89, 50/6.0 s; multiword add 224, 70/1.2 s; Skein 1,352, 5,366/56 s. ISA evaluation is **additional**, respectively 7.8/173/37/500 s. These are decompilation costs, not end-to-end functional-proof times; inference counts ≠ script lines. | [Paper §§I, III; Fig. 1](https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf): “Decompilation also automatically proves a theorem, which we call a certificate theorem, relating the new function to the machine code from which it was extracted.” “Split the CFG into separate decompilation rounds, i.e. separate inner loops from enclosing outer loops where possible.” “Any verification that uses such extracted function must prove that the returned cond is equal to true (for relevant input values)”. [CakeML §9](https://cakeml.org/cpp17.pdf): “Each bytecode instruction is mapped to a block of x86-64 instructions, and the translation was manually verified using decompilation tools.” Exact table + termination caveat in §A2. | **Inference:** a recursive Lean model plus kernel-checked block/certificate theorems fits FVA; extraction need not be trusted. HOL's nonterminating `while` operator does not directly become Lean total recursion: use fuel, a proven measure, or relational semantics with termination separate. The model is proof scaffolding only if final claims remain about the linked Wasm semantics. |
| A3 | Binary-level refinement/simulation proofs at scale: seL4 binary verification (Sewell, Myreen, Klein PLDI 2013), CompCert/translation validation; how a loop's simulation relation is stated | seL4 reduces C + binary to graph IR, proves procedure-by-procedure refinement, treats calls by contracts, and pairs loop cutpoints: corresponding values satisfy equality predicate P on corresponding visits; offsets/n-step induction handle some unrolling. CompCert proves pass-wide state simulation, including statement/PC, continuation/stack, environment/register + memory correspondence; loops are covered by the transition theorem. seL4's SMT-based tool is **not** a Lean-kernel-replayed implementation. | seL4 Table 1: -O1 11,736 instructions; 260 pairings, 234 successes, 26 aborted; 59m proof. -O2 12,299 instructions; 225 pairings, 145 successes, 18 failures, 62 aborted; 4h 23m proof. Decompilation with certificates adds 6–8h. Loop heuristic: first candidate succeeds in 33/43 loops; other 10 average 15 attempts, worst 84. Whole-program figures, not one huge function; partial coverage matters. | [seL4 §§3.3.5, 4; Table 1](https://www.cl.cam.ac.uk/~mom22/pldi13.pdf): “the checker will prove by induction that for each visit to b_sp along the binary execution path, c_sp is also visited with the variable state related by P.” “In 33 of our 43 loops, the induction succeeds for the first candidate P” / “an average of 15 attempts” / “84 attempts”. [CompCert](https://compcert.org/doc/html/compcert.backend.RTLgenproof.html): “Agreement between the Cminor statement under consideration and the current program point in the RTL control-flow graph” / “Agreement between the Cminor continuation and the RTL control-flow graph and call stack”. Exact transition theorem + counts in §A3. | **Inference:** relate Wasm loop-head states to model arguments; prove one model transition corresponds to a finite semantic path, then induct. Include memory, locals, operand/control-stack shape + footprint in that relation/path theorem. For all-execution claims, also cover every machine continuation/branch or justify determinism + progress; existential simulation of one successful run alone is weaker. |
| A4 | s2n-bignum (HOL Light): loop proof method (e.g. ENSURES_WHILE_*), footprint statements (MAYCHANGE, nonoverlapping), per-function instruction counts + proof sizes | Direct symbolic execution inside invariant rules: `i ↦ registers ∧ copied prefix ∧ untouched source suffix`; prove entrance, one iteration, backedge, exit. `nonoverlapping` preconditions discharge alias/code-overwrite hazards. **`MAYCHANGE` is an initial/final frame—not a per-step read/write footprint.** Event/safety proofs supply the stronger property. | CAV §8.1: copy 16 instructions / functional proof 180 lines; inverse 1,033 / 2,303 lines; combined correctness + constant-time 2,633 lines. Pinned snapshot measurements: copy 16 instructions / 180 file lines; add 56 / 647; inverse 1,033 / 3,624. File lines include opcodes, setup, helpers + multiple theorems. Per-function checking times: **none found** in inspected paper/docs or timing searches (§A4); no HOL replay run here. | [CAV §8.1](https://cdn.amazon.science/56/20/f6b40ee84e7b8633ca1053499aff/relational-hoare-logic.pdf): “The bignum_inv_p25519 routine instead is a 1033-instruction program” / “The functional correctness proof is 2303 lines long.” [Pinned copy proof](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/arm/proofs/bignum_copy.ml#L42-L54): `MAYCHANGE [memory :> bignum(z,val k)]`. [SOUNDNESS §A4](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/SOUNDNESS.md#L132-L148): “The frame condition constrains only what is *written* (and only by comparing initial and final states)” / “**Transient writes** (writing then restoring a value) are not excluded either.” Exact excerpts + measurement commands in §A4. | **Inference:** strongest direct template for U19 = invariant cutpoints plus reusable symbolic blocks. Prove every load/store address lies in the allowed ranges on every execution prefix, including intermediate writes + callee accesses. A destination-only final-memory theorem may be a corollary, never a substitute. |
| A5 | Direct symbolic stepping vs refinement: any head-to-head comparison or reported tradeoff (proof effort, robustness to recompilation / new compiler versions, re-proof cost per release) | **No controlled same-binary direct-vs-functional-refinement comparison found.** Original HOL4 paper compares GC proof lengths across different projects/provers and demonstrates tiny cross-architecture proof reuse; neither establishes a general effort ratio. Realistic optimized-code evidence: s2n composes equivalence proofs across transformations; seL4 reports compiler-version-sensitive stack heuristics. Quantitative per-release re-proof cost: **none found**. | HOL4 GC comparison: other Coq proof 7,775 lines vs approximately 2,000 HOL4 lines, confounded. Linked-list extracted-function equality across ARM/x86/PowerPC: three-line proof, tiny example. s2n: 15 optimized/reference pairs, 19k proof lines; no direct-baseline comparison. HOL4 old/new decompiler timing in A2 is an internal implementation comparison, not route (a) vs (b). | [HOL4 original §II-C/D](https://www.cl.cam.ac.uk/~mom22/decomp.pdf): “The proofs by McCreight et al. (7775 lines) are much longer than our (approximately 2000-line) proofs, which suggests that decompilation aided our verification effort.” / “in this case a three line HOL4 proof”. [seL4 §4.2](https://www.cl.cam.ac.uk/~mom22/pldi13.pdf): “During the project, we switched gcc versions a few times. Each time the stack heuristic required some fine-tuning.” [CAV §8.2](https://cdn.amazon.science/56/20/f6b40ee84e7b8633ca1053499aff/relational-hoare-logic.pdf): “Overall, we checked the equivalence for 15 pairs of arithmetic routines, amounting to a total of 19k lines of proofs.” Search record + limits in §A5. | **Inference:** do not select refinement on an alleged literature speedup. Direct proofs avoid model/simulation setup; refinement can retain model correctness while redoing only the artifact link, but that link still changes with code. The planned matched-loop spike is needed; include model construction, simulation, footprint + kernel replay in the comparison cost. |
| A6 | Reported causes of failure / blow-up in large machine-code proofs (term size, simp time, memory model, aliasing) + their fixes | Confirmed: expression duplication → abbreviate intermediates; expensive rewriting/frame composition → theorem normal forms with direct composition; address aliasing → bounded/disjoint-region facts; optimized/irreducible CFG → paired cutpoints + compositional blocks (heuristics still fail); full-ISA unfolding → simplify concrete instruction effects before proof. Abbreviation can itself hide address/counter facts: protect those expressions. | HOL4 Skein composition 5,366→56 s, ISA evaluation separately 500 s (A2). seL4 -O2 has 18 failed pairings; nested-loop functions aborted (A3). TACAS memory-usage study: 251/352 functions, 12,252 instructions, 65 loop-bearing functions, 1,047 manual lines. This is partial memory-usage coverage, not full functional correctness. Islaris Fig. 12 examples ≤48 assembly lines: useful mechanisms, not LZ4-scale evidence. | [CAV §8.2](https://cdn.amazon.science/56/20/f6b40ee84e7b8633ca1053499aff/relational-hoare-logic.pdf): “eagerly abbreviates the common outputs of the instructions with fresh variables to avoid exponential explosion of the sizes of the output expressions.” [HOL4 §II](https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf): “composition was the main performance bottleneck: often involving simplification through rewriting and calculation of a separation logic ‘frame’.” [TACAS §4](https://www.ssrg.ece.vt.edu/papers/tacas20.pdf): “SCF explodes. The issue occurs mostly when loops have multiple entries.” [Pinned s2n §4.5](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/doc/program_equivalence.md#L635): “Preventing abbreviation of memory addresses and loop counter”. More limits + fixes in §A6. | **Inference:** use named state variables + cached block lemmas; bounded simplification instead of repeatedly unfolding the whole stepper; keep addresses/counters visible to arithmetic. Measure Lean elaboration/kernel time + term size separately. Cited seconds cannot predict Lean/Wasm cost. Overlapping LZ4 matches require the actual sequential-copy semantics; do not invent disjointness to make a proof easy. |

## A1 — classification details + proof obligations

- **Direct invariant / symbolic-step example:** pinned s2n tutorial https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/arm/tutorial/loop.ml. Source excerpt: “ENSURES_WHILE_PAUP_TAC is one of several tactics for declaring a hoare triple of a loop.” The script separately labels “entrance to the loop”, “The loop body”, “Prove that backedge is taken if i != 10”, and “Loop exit to the end of the program”. The invariant relates registers to the iteration counter; symbolic execution handles the finite segments.
- **Generated cutpoint assertions / footprints:** https://www.ssrg.ece.vt.edu/papers/tacas20.pdf, §3.3: “The while rule is based on a loop invariant I. If the memory usage of one iteration of function body f is constrained to the set of memory regions M, then that holds for the entire loop.” “For each loop entry, it is required to manually apply the weaken rule to show that the postcondition of the block before entry implies the loop invariant.” Its generated invariant is a proposed proof ingredient, not a trusted oracle.
- **Refinement need not be global instruction lockstep:** https://cdn.amazon.science/56/20/f6b40ee84e7b8633ca1053499aff/relational-hoare-logic.pdf, §8.2: “Its original implementation in the s2n-bignum library includes a nested loop structure” / “We verified the functional correctness of the optimized Montgomery reduction by transitively composing equivalence proofs with the original correctness proof after each optimization stage.” / “For each optimization, we applied sequential composition of equivalences between each basic block pair and induced the equivalence of the whole loop.” This is code↔code equivalence, not a Lean functional model, but demonstrates the shared block-composition mechanism.
- **Inference for FVA:** keep four obligations distinct: artifact linkage; all-input functional behavior under stated preconditions; termination/progress if claimed; every-step footprint. Extraction/simulation does not discharge the other obligations automatically. The sources support methods, not a claim that the current FVA implementation already has their automation.

## A2 — decompilation measurements, termination + CakeML

Source: https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf, Fig. 1. Verbatim table (layout extraction):

```text
ARM machine code                      instr.         time/cost of old       time/cost of new            reduction            model eval.
sum of array (Sec. I-A)                   4          2.5 s (73,039 i)          0.3 s (4,019 i)       86 % (94 %)          7.8 s (1.5 Mi)
copying garbage collector [10]           89        50 s (1,526,281 i)         6.0 s (53,301 i)       88 % (97 %)          173 s (40 Mi)
1024-bit multiword addition            224         70 s (1,029,685 i)         1.2 s (10,802 i)       98 % (99 %)          37 s (8.9 Mi)
256-bit Skein hash function          1,352     5,366 s (21,432,926 i)      56 s (1,842,642 i)        99 % (91 %)         500 s (105 Mi)
```

Caption: “The cost is given in seconds (s) and number of primitive higher-order logic inferences (i) in HOL4 [16]. The cost of evaluating the ISA model is separated as this cost is independent of decompilation approach.” These timings are not measured by this research task, and the table is not a proof-effort comparison between U19's routes.

§III-C: “Crucially, while can be defined in (higher-order) logic without a termination proof [7], which is important because most of the functions the decompiler extracts do not terminate for all inputs. However, note that our Hoare triples are total-correctness Hoare triples, i.e. we need to know that our use of while terminates for certain inputs”. The extracted `cond` includes the existential termination condition. **Inference:** a certificate conditional on `cond` is not an unconditional all-input theorem.

Source: https://cakeml.org/cpp17.pdf, §9: “The first version of the CakeML compiler (Kumar et al. 2014) supports compilation down to x86-64 assembly via a bytecode IL. Each bytecode instruction is mapped to a block of x86-64 instructions, and the translation was manually verified using decompilation tools. Our approach here goes further by compiling down to an assembly IL.” The later compiler's verified-compilation architecture is distinct from decompiling arbitrary clang output into a model.

## A3 — seL4 coverage + simulation relation; CompCert diagram

Source: https://www.cl.cam.ac.uk/~mom22/pldi13.pdf, Table 1:

```text
                                 gcc -O1         gcc -O2
Instructions in Binary           11 736          12 299
Decompiled Functions             260             259
  - Placeholders                                 3
Function Pairings                260             225
Successes                        234             145
Failures                         0               18
Aborted                          26              62
  - Machine Operations           21              13
  - Nested Loops                 3               2
  - Machine Operations Inlined   2               47
Time Taken in Proof              59m             4h 23m
```

§4.1: “A full decompilation run with proof certificates takes an additional 6–8 hours on modern hardware.” “Proof timings are taken on a single core of an Intel Core 2 Duo E8400. The majority of the time taken is spent in the SMT solvers.” Do not treat these as one modern Lean replay time.

§3.3.5: “The rule names a C split point c_sp, a binary split point b_sp, an equality predicate P and a bound n.” “P holds on the values of the variables at the i-th visit to c_sp and b_sp respectively.” “Having established that the sequence of visits to b_sp is matched at c_sp, we consider three cases on the length of the sequence. If the sequence is infinite, then the binary execution and C execution are both non-terminating, and this is a valid refinement.” Thus refinement alone does not assert all-input termination.

§3.3.5 heuristic results: “In 33 of our 43 loops, the induction succeeds for the first candidate P for which I_0, I_1, . . . I_(n−1) hold.” “In the remaining 10 cases the early check was mostly irrelevant and an average of 15 attempts were required to find a successful condition.” “The variation in these numbers is large, with the worst offending loop contributing 84 attempts, nearly half the total.” Subscript typography normalized; words/numbers retained.

Trust boundary: §3 introduces “our SMT-based proof tool”; §3.3.2: “These values are all encoded in the SMTLIB2 QF_ABV logic (quantifier-free formulae over arrays and bit-vectors).” **Unconfirmed:** no Lean-kernel replay of the SMT proof obligations was found in the inspected paper. Treat the architecture as precedent, not an acceptable FVA trust extension.

CompCert official state relation, https://compcert.org/doc/html/compcert.backend.RTLgenproof.html:

```coq
Theorem transl_step_correct:
  forall S1 t S2, CminorSel.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2,
    (plus RTL.step tge R1 t R2 \/
      (star RTL.step tge R1 t R2 /\ lt_state S2 S1))
    /\ match_states S2 R2.
```

The source describes `match_states` as agreement of statement/PC, continuation/control-flow graph/call stack, and local/register environments. Its `match_state` constructor also requires `Mem.extends m tm`. The theorem permits nonempty target stepping or well-founded stuttering; loops do not require enumerating all iteration counts.

Generic simulation, https://compcert.org/doc/html/compcert.common.Smallstep.html, `fsim_simulation`:

```coq
forall s1 t s1', Step L1 s1 t s1' ->
forall i s2, match_states i s1 s2 ->
exists i', exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
  /\ match_states i' s1' s2'.
```

**Inference:** for a proof-side model, the relation should expose exactly the machine facts needed by block lemmas; avoid carrying the entire concrete machine state when a projection suffices. A source→target existence theorem needs the usual determinism/progress/behavioral arguments before it supports an all-target-executions statement.

## A4 — s2n loop invariant, frame limitation + measurements

Pinned source revision: https://github.com/awslabs/s2n-bignum/tree/573ea98f6a2eea3172f6146f83b86b9e526ce2dd . Read-only clone; no source execution or HOL replay.

Copy proof https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/arm/proofs/bignum_copy.ml#L42-L54:

```ocaml
nonoverlapping (word pc,0x40) (z,8 * val k) /\
(x = z \/ nonoverlapping (x,8 * MIN (val n) (val k)) (z,8 * val k))
...
(MAYCHANGE [PC; X2; X4; X5] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
 MAYCHANGE [memory :> bignum(z,val k)])
```

Invariant, same file lines 107–117:

```ocaml
ENSURES_WHILE_UP_TAC `n:num` `pc + 0x10` `pc + 0x1c`
 `\i s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word n /\
        read X3 s = x /\
        read X4 s = word i /\
        bignum_from_memory(z,i) s = lowdigits a i /\
        bignum_from_memory(word_add x (word(8 * i)),n - i) s =
        highdigits a i`
```

This handles arbitrary runtime length by induction, not by a fixed fuel unroll. Aliasing is not ignored: the precondition allows exact in-place copying or disjoint buffers. That is not a license to impose disjointness on a different algorithm whose contract allows overlap.

Critical footprint caveat, https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/SOUNDNESS.md#L132-L148:

> The functional-correctness specifications alone do not fully guarantee memory safety. The underlying memory model is a flat byte-addressed array with no notion of "valid" or "allocated" addresses; reads and writes always succeed. The frame condition constrains only what is *written* (and only by comparing initial and final states), so in principle:
>
> - **Out-of-bounds reads** are not excluded by a functional correctness proof.
> - **Transient writes** (writing then restoring a value) are not excluded either.

Stronger infrastructure, same section:

> The same safety proof infrastructure introduced for constant-time (see A3) also proves memory safety: it establishes that all memory reads and writes performed by a function fall within the bounds declared in its specification.

Paper measurements, https://cdn.amazon.science/56/20/f6b40ee84e7b8633ca1053499aff/relational-hoare-logic.pdf, §8.1:

- “The bignum_copy routine is relatively small, comprising 16 instructions” / “The functional correctness proof is 180 lines.”
- “The bignum_inv_p25519 routine instead is a 1033-instruction program” / “The functional correctness proof is 2303 lines long.”
- “The constant-time proof, using the unary embedding of Definition 8 combining correctness and constant-time proofs, is 2633 lines long.”

Reproducible snapshot measurements (derived counts, not quotations from the paper). For each `name ∈ {copy, add, inv_p25519}`:

```bash
f="arm/proofs/bignum_${name}.ml"
rg -c '^  0x[0-9a-f]+[;, ]' "$f"
wc -l < "$f"
```

Verbatim measurement output:

```text
bignum_copy: instructions=16 source_lines=180
bignum_add: instructions=56 source_lines=647
bignum_inv_p25519: instructions=1033 source_lines=3624
```

Each counted opcode line carries one decoded ARM instruction comment; copy list lines 18–33 explicitly runs from `arm_CMP` to `arm_RET`. Stable source URLs: [copy](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/arm/proofs/bignum_copy.ml), [add](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/arm/proofs/bignum_add.ml), [inverse](https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/arm/proofs/bignum_inv_p25519.ml). Script-file size differs from a paper's singled-out proof size; the inverse discrepancy is not evidence of a regression.

**None found — per-function replay times:** searched CAV paper §8, s2n README, SOUNDNESS, program-equivalence docs + loop tutorial; web queries `"s2n-bignum" "proof" "checking time"`, `"s2n-bignum" "bignum_inv_p25519" "seconds" proof`. Results did not give a confirmed time for these specific proofs. No claim that such a measurement does not exist elsewhere.

## A5 — evidence strength, robustness + search limits

Original HOL4 paper https://www.cl.cam.ac.uk/~mom22/decomp.pdf, §II-D:

> Similar Cheney collectors have been verified by Birkedal et al. [6] (on paper) and McCreight et al. [7] (using Coq). The proofs by McCreight et al. (7775 lines) are much longer than our (approximately 2000-line) proofs, which suggests that decompilation aided our verification effort.

This is a **reported qualitative suggestion with a numerical comparison**, not a controlled experiment on the same binary/specification/prover/tooling. Its largest examples are described as “approximately one hundred machine instructions.”

§II-C:

> Minor differences, such as register names, conditional execution (ARM), variable instruction length (x86) and some instruction reordering (PowerPC example has load before increment), disappear in the functional description of the behaviour of the code. As a result the extracted functions can be proved equal by a short proof, in this case a three line HOL4 proof.

This supports possible proof reuse when extracted functions normalize similarly. It does not establish robustness for arbitrary compiler transformations or nested-loop code.

seL4 https://www.cl.cam.ac.uk/~mom22/pldi13.pdf, §4.2:

> The exact use of the stack depends on the compiler, which means that our heuristics are fragile and at present only target recent versions of gcc. During the project, we switched gcc versions a few times. Each time the stack heuristic required some fine-tuning.

No elapsed re-proof/maintenance effort is quantified there. At higher optimization, §4.1 reports failure to find split points “usually because of loop unrolling, loop invariant code motion and other loop structure optimisations.”

s2n https://cdn.amazon.science/56/20/f6b40ee84e7b8633ca1053499aff/relational-hoare-logic.pdf, §8.2: “Overall, we checked the equivalence for 15 pairs of arithmetic routines, amounting to a total of 19k lines of proofs.” This supports reuse through equivalence; it does not measure savings over directly re-proving each optimized routine.

**None found — matched direct/refinement study or per-release re-proof cost.** Search surfaces: WebSearch scholarly results, Cambridge/Myreen papers + decompilation project page, seL4 PLDI paper, CAV relational-logic paper + s2n repo/docs, TACAS memory-usage paper, Islaris paper and related work. Query phrasings included:

```text
"decompilation" "direct" "proof" "effort" machine code verification invariants
"machine code" "loop invariants" "decompilation" "proof effort"
"decompilation into logic" "proof effort" comparison direct
"direct" "decompilation into logic" benchmark proof comparison
"machine-code verification" "compiler versions" proof reuse
"decompilation into logic" "compiler" "versions" proof
"s2n-bignum" "proof" "recompil"
"s2n-bignum" "compiler versions"
```

Later phrasings mostly resurfaced the same papers or irrelevant hits. This is a bounded literature search, not a systematic-review completeness claim. No source supplies a defensible direct/refinement effort ratio for Lean/Wasm/LZ4.

## A6 — causes, fixes + scope limits

### Expression growth / proof composition

HOL4 https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf, §II:

> In the new approach, we carefully state the intermediate theorems so that composition of intermediate results can be done in a handful of fast operations. In the previous approach, composition was the main performance bottleneck: often involving simplification through rewriting and calculation of a separation logic ‘frame’.

CAV https://cdn.amazon.science/56/20/f6b40ee84e7b8633ca1053499aff/relational-hoare-logic.pdf, §8.2:

> For the identical portion, the tactic performs lock-step symbolic simulation and eagerly abbreviates the common outputs of the instructions with fresh variables to avoid exponential explosion of the sizes of the output expressions.

The same paragraph says user-supplied bit-vector equality theorems help convergence on optimized ranges. This is proof-producing tactic infrastructure, not a requirement to trust an external solver.

Pinned s2n docs https://github.com/awslabs/s2n-bignum/blob/573ea98f6a2eea3172f6146f83b86b9e526ce2dd/doc/program_equivalence.md, §2.5:

> `PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC` only works when the program is supposed to have a *constant* number of steps to finish — it cannot handle a program containing a loop that iterates a symbolic `n` times, because it needs to statically unroll every step.

This is a limitation of that **lifting tactic**, not of s2n's invariant rules. Do not generalize a successful fixed-count symbolic-execution demo to unbounded input lengths.

Same doc §4.5:

> Abbreviating a register that holds a memory-access base address (e.g. `word_add z (word (8 * 4 * i))`) or a loop counter (e.g. `word (k4 - (i + 1))`) would make subsequent symbolic simulation of `ldr`/`str` unable to identify from which memory invariants values should be loaded.

Its fix is per-instruction `regs_no_abbrev_left/right`, computed by backward taint analysis. **Inference for Lean:** abbreviate large arithmetic values while retaining the address/counter forms needed by the chosen arithmetic + memory lemmas.

### Control-flow / memory proof scale and limitations

TACAS https://www.ssrg.ece.vt.edu/papers/tacas20.pdf, Fig. 4:

```text
Binaries       Function Count Instruction Count Loops Manual Lines of Proof
xenstore       2/6            100               0     6
xen-cpuid      2/3            210               2     39
qemu-img-xen   247/343        11,942            64     1,002
Total          251/352        12,252            65     1,047
```

The loop column is explained as “functions with loops that were verified”; do not treat 65 as a count of every syntactic loop. §4: “Some of the functions analyzed have over 300 instructions and over 100 basic blocks.” / “The final category is functions whose SCF explodes. The issue occurs mostly when loops have multiple entries.” Other listed unsupported cases include indirect calls/jumps, difficult mixed arithmetic/bitwise addresses, an instruction, and recursion. No universal scalability guarantee follows from the successfully verified subset.

Scope/trust limits, §2:

> The term memory usage formally denotes an overapproximation of the memory written to by a function. Thus, any address that is not enclosed in one of the regions of M, is guaranteed to be preserved. Set M, however, will also include the memory regions read by the function, for verification purposes.

Thus this paper is not by itself evidence for **separate exact read-vs-write bounds** matching U19. The theorem uses an overapproximation + assumptions. §2 also warns:

> One exception is the memory region relations. They are assumptions, and if they are internally inconsistent this leads to a vacuous truth.

**Inference:** FVA must discharge compatibility/nonvacuity of any chosen memory-layout preconditions against its intended input domain; automatically proposing an alias condition does not make that condition an acceptable contract.

### Full semantic-model complexity

Islaris https://people.mpi-sws.org/~dreyer/papers/islaris/paper.pdf, §1:

> in the Coq version even simple definition unfoldings take an unreasonably long time or fail to terminate.

Its method separates “the irrelevant complexity from the inherent complexity” using instruction traces simplified under concrete opcodes/system constraints, then higher-level separation-logic proofs. §6:

> The larger case studies use intermediate specifications for some instructions to let these be verified in parallel

and:

> further performance improvements are possible (especially when using many registers and in the bitvector automation).

Fig. 12 labels size as **lines**, not instructions; the largest assembly listing shown is RISC-V binary search at 48 lines. Source rows:

```text
Test        ISA   asm  ITL  Spec Proof Isla Coq
memcpy      Arm     8  169    20    55    6 9/2/8/-
bin.search  Arm    32  741    25   146   25 54/16/37/19
            RV     48  801    25   108    5 63/22/37/21
```

Times are seconds; Coq subdivisions = automation / side-condition tactics / Qed / intermediate instruction proofs. These are **not** LZ4-size benchmarks. §6 explicitly says: “Our examples are not large in instruction count”. Base approach adds Isla + SMT solver to its trusted base; RISC-V trace validation can remove that dependency for the shown example. It is a useful architectural source, not an implementation FVA can adopt without kernel-checked certificates.

### Extraction scale is not program correctness scale

Leviathan/CPP paper https://ssrg.ece.vt.edu/papers/cpp2019.pdf, §8.1:

> We successfully decompiled-into-logic the binary of gcc 4.9 with approximately 361K lines machine code in 1.3 hours on a machine with a 6-core Intel i9-8950HK CPU running at between 2.9 and 4.8Ghz.

This demonstrates extraction throughput, **not** an all-input functional correctness theorem for GCC or all its loops. The paper's Fig. 8 classifies its property as “Big-Step Equivalence”. In its smaller floating-point case, §7 reports:

> A cut can reduce the number of instructions to be symbolically executed.

and:

> Without introducing the cut-point, a significantly larger amount of instructions are executed twice (or more). Introducing a cut thus improves verification time.

**Inference for U19:** summarize rejoining paths once and reuse summaries. Do not count an extracted function's size, successful bounded runs, or model equality as the desired all-input decoding/footprint result.

researcher-1-DONE-1
