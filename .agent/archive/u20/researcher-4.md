# researcher-4 — agent fit: proof scaling over compiled / low-level code

Primary-source/textual survey; no upstream proof build or repo gate run. Source-reported results ≠ independently replayed proofs. **Finding:** no controlled agent comparison chooses A/B/C. Positive compiled-code and decoder developments converge on *human-designed abstractions + reusable contracts + mechanical execution + agent-sized mathematical goals*. A functional model alone does not solve invariant discovery; raw generated VCs can be as hostile as raw machine states. Candidate beyond A/B/C = an orthogonal contract-first proof-producing WP/VC interface, not a fourth trusted semantic route. Details below qualify every headline rate.

| id | question | answer | numbers | source (URL + verbatim excerpt) | applicability to FVA |
|---|---|---|---|---|---|
| R4.1 | Published LLM-agent results on compiled/machine code; method + success rates | **Binary proofs are demonstrably agent-feasible with substantial reusable infrastructure; s2n's low headline is not an interactive-agent test.** s2n = ISA symbolic execution / arithmetic tactics, query-only generation; Theorem/Anthropic = Rocq proofs over compiled RISC-V at much larger scale. **LZO full-content round-trip headline unconfirmed: published harness checks decompressed length, not content.** No controlled A/B/C comparison found. | s2n GPT-5.3-Codex: 101/2,284 medium; 121/2,284 high; **0/859 functional-correctness tasks** in either mode (table totals). Theorem reports 239 entry points / 123 libraries, median 18,000 instructions; no attempted-target denominator supplied in main post. | [s2n §A.5–A.7](https://arxiv.org/html/2603.14628v2): `restricted read-only sandbox with shell access, databases, and web search disabled` / `Zero-shot, query-only assessment` / `medium-effort run solved 101 / 2,284 problems (4.4%) and the high-effort run solved 121 / 2,284 (5.3%)`; table: `fc_arm ... 437 ... 0 ... 0.0%`, `fc_x86 ... 422 ... 0 ... 0.0%`. [Anthropic](https://www.anthropic.com/research/formal-verification): `239 entry points across 123 different OSS-Fuzz libraries` / `median length of 18,000 RISC-V instructions` / `a fuzz test for the LZO compression algorithm asserts that if you compress an input, then decompress it, the result is the same as the original`. | Feasibility evidence, not method superiority or predicted U19 success. Strong warning against using s2n 5.3% as a success estimate for a Lean coding agent with feedback, examples + library access. Theorem's bounded-input no-crash theorem ≠ FVA R1–R3; details under R4.1. |
| R4.2 | Agent success on loop invariants/function contracts by proof interface | **Structured contract/invariant generation + verifier-specific repair works on small source programs; extracting a functional model does not make invariant discovery automatic.** AutoVerus separates initial invariants, generic strengthening + error-class repair; Aeneas/Hax experience report still needed humans for extracted-loop invariants. No matched low-level copy/parser/decoder experiment comparing the interfaces found so far. | AutoVerus 137/150 (91.3%) within ≤3 full attempts; 122 first-attempt; Diffy invariant tasks 38/38 vs baseline 5/38. DafnyBench Claude 3 Opus 67.8±1.7%, including 26.9% no-LLM successes, ≤10 feedback attempts. Aeneas/Hax report = two AI-closed bounds theorems + informal experiments, not a solve-rate benchmark. | [AutoVerus §6–7](https://arxiv.org/html/2409.13082): `137 out of 150 (91.3%)` / `122 tasks in its first attempt` / `baseline ... only 5 out of 38 Diffy tasks`; [DafnyBench §4](https://arxiv.org/html/2406.08467): `Claude 3 Opus ... 67.8 ± 1.7` / `No LLM ... 26.9`; [Rust-to-Lean §5](https://arxiv.org/html/2605.30106v1): `Loop invariants on Aeneas-extracted recursive functions ... remained a manual task` / `two theorems that Aleph closed ... plus informal experiments`. | Evidence favors constrained outputs, typed error feedback, immutable implementations/specs + reusable contracts. Source-language SMT success ≠ Lean-kernel compiled-code success; no causal A/B/C ranking from cross-paper headline rates. |
| R4.3 | Large agent-written proofs; maintainability + tooling | **Large AI proofs use hybrid abstractions, milestone contracts + CI, not a demonstrated clean-proof guarantee.** CLean links pure combinatorics to Clight/separation logic; mesh separates reviewed specs/impl/proofs, uses reviewed informal plans + incremental Lean LSP; lean-zip refines fast code to simple references under an immutable round-trip CI gate. Mesh explicitly admits design debt. | CLean ≈20k Lean lines for 266 C lines / 7 loops; mesh reports >60k proof lines; lean-zip >1,100 theorems / ≈32k proof lines; SymCrypt ≈5.1k agent theorems / 125 KLOC proof bodies. Source-reported sizes, not independently counted productivity. | [CLean](https://www.certora.com/blog/formally-verifying-zlib-memory-safety-with-lean): `proofs were written almost entirely by LLMs`; [mesh c537025 README:5,76](https://github.com/schildep/verified-3d-mesh-intersection/blob/c537025f69511110108acc9608dc1cdb19025057/README.md#L5): `over 60,000 lines of Lean proofs` / `nowhere near as clean and do not follow a cohesive design`; [lean-zip 2f7a63 README:20–28](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/README.md#L20-L28): `more than 1,100 theorems across ~32k lines of proof` / `pull requests that could not merge unless the round-trip proof still went through`. | Reuse/refinement + tooling is a credible workflow; neither mesh nor lean-zip proves an unchanged foreign binary. CLean stops at Clight, not compiler correctness. Zip's native C replacements are trusted against Lean reference bodies. Details + exact workflow excerpts below. |
| R4.4 | Agent friction in symbolic execution vs model reasoning; mitigations | **Observed friction = library orientation + tactic/interface failure; formal evidence does not isolate a causal method effect.** FVA's own runs spent substantial context on internals before failed builds. s2n describes machine-state rewriting/aliasing/endianness but baseline denies tools; Theorem reports proof sharing cuts token use. | FVA archive: ≈20–40% internal-source context; ≈half internal reads before first failed build (post-hoc, indicative). Theorem reports 17% fewer tokens with shared proofs; no independent rerun. | [/home/eturkes/Projects/fva/.agent/archive/maintain-bench-direction.md:29–31](../../.agent/archive/maintain-bench-direction.md): `≈ 20–40 % of context volume` / `≈ half the internal reads precede the first failed build (orientation, not only tactic debugging)` / `No causal fraction of the token gap identified`. [Anthropic](https://www.anthropic.com/research/formal-verification): `When given access to this shared workspace, agents needed 17% fewer tokens than when they worked alone`. | Strong reason to expose a small stable contract/tactic API + searchable examples + callee/block summary reuse. These are evidence-backed design hypotheses, not an established ranking of A/B/C. |
| R4.5 | Agent-oriented candidate beyond {hand stepping, model refinement, automated blocks} | **Evidence points to an orthogonal fourth *interface*: contract-first, proof-producing WP/VC generation, with kernel-proved code reshaping + agent-synthesized invariants/math lemmas.** Do not treat A/B/C as exclusive methods. SymCrypt's `decompose` kernel-proves folding of large extracted bodies; `@[step]` contracts + `step*` reduce execution to mathematical side goals. Talos exposes compositional WP for Wasm. This combines B/C with reusable contracts rather than inventing another trusted semantic link. | SymCrypt reports ≈5.1k agent theorems / 125 KLOC proof bodies; seven-hard-proof case set solved by Opus 5 in single sessions. Talos has no agent success-rate measurement confirmed. | [SymCrypt §5.2–5.6](https://arxiv.org/html/2609.15648v1): `@[step] ... database of code properties ... without having to unfold its definition` / `decompose ... a theorem that proves the transformations preserve functional equality` / `effectively used by agents` / `skill files ... documentation and examples`. [Talos pinned README](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/README.md#reasoning-foundation): `structured, compositional proofs for loops, branches, and function calls without re-unfolding the interpreter at every step`. | Candidate for an agent-facing Wasm proof API: prove `memcpy`/`memmove`/overlap-copy contracts once; emit block/call VCs mechanically; agents see buffer slices + arithmetic + semantic invariants, not entire machine states. Preserve FVA's existing small-step/access/termination theorem via kernel-checked soundness. This is an inference/design candidate, not a measured U19 winner. |
| R4.6 | Direct decoder/copy-agent evidence + failure costs | **liblzma/VST = unusually close task analogue:** functional models + buffer representations + function contracts, then agent symbolic execution/entailments. Large monolithic goals required warm incremental checking + mechanical goal extraction; most proof bulk was invariant reconstruction, not instruction stepping. | 27 closed bodies; `lzma_bufcpy`: 18 C / 392 proof SLoC; `dict_repeat`: 47 C / 2,081 proof SLoC; largest decoder ≈183k proof SLoC; 1,595 sessions over 70 days (not labor savings). | [liblzma paper §3, §6](https://arxiv.org/html/2608.29716v1): `functional Model ... abstract state and transition` / `Proof agents ... symbolic execution and entailment solving`; table `lzma_bufcpy ... 392 ... 18`, `dict_repeat ... 2,081 ... 47`; `only about 2% ... forward steps` / `18-conjunct ... argument, written out 63 times`; `no human-only baseline is available`. | Supports contract reuse + invariant factoring + agent-sized residual goals, not trusting giant raw state dumps. Boundary is **transformed** C→Clight with imported contracts; final source-equivalence and caller/callee closure remain open, so not an unchanged-binary success claim. |

## R4.1 — Compiled-code primary evidence

### Evidence-to-method matrix (no cross-paper rate comparison)

| work | proof interface actually exposed | agent outcome | scope / attribution limit |
|---|---|---|---|
| s2n-bignum-bench | Query-only HOL Light tactic expression for ISA-state theorem; symbolic execution in underlying library | Headline 5.3% high effort; zero routine functional-correctness tasks (§A.7 quotes below) | No shell/proof-check feedback; not an autonomous repo agent and not a matched method comparison. |
| Theorem / Anthropic | Binary semantics + agent-authored short functional/output specs, then binary-to-spec proofs + explicit execution facts | Large source-reported completed corpus; pinned public subset confirms agent-produced proof artifacts (quotes below) | Most proof bulk = tables/runtime/ASan; full LZO content correctness not established by harness; no attempted-target solve rate. |
| MachCSL | Hardware-level Iris concurrent separation logic + function contracts + manual abstraction design | Compiled xv6 case study finished; authors explicitly report agent failure without abstraction and success after imposing it (§R4.4) | Entire framework/development/human guidance; one case study, not matched rate. |
| Talos | Wasm WP + instruction lemmas, loop invariant/Löb + separate well-founded termination | Pinned optimized Rust gcd theorem exists (§R4.1 Talos below) | No attributed AI solve rate/time found; repo agent instructions do not prove autonomous performance. |
| LNSym | Arm machine-code symbolic simulation; bit-vector discharge | Infrastructure exists; a firsthand LLM-assisted attempt reports only tiny-function success, larger examples exhausting memory | Unpublished code/unspecified resource budget; anecdote, not general failure rate. |
| SymCrypt/Aeneas | Source-to-pure-model extraction + kernel-proved reshaping + contract stepping | Large agent proof corpus + seven-hard-proof evaluation (§R4.2/5) | Not compiled bytes; no native/raw-Wasm control arm. |
| riscv-decomp | Machine-certified emission of a recursive body; user proves equations + induction over emitted function | No agent-performance measurement in inspected exemplar/certificate/scope files | Register-only single-loop fragment; loads/stores/calls/nested loops excluded; not a demonstrated LZ4-scale agent method. |


### s2n-bignum-bench (query-only baseline, not interactive agent)

Source: https://arxiv.org/html/2603.14628v2, §3, §5, Appendix A.

- Proof interface, verbatim: `decomposing the program at specific program-counter offsets, symbolically executing each segment by rewriting through ISA-specific decode and execute semantics, and simplifying the resulting symbolic state terms at each step.`
- Construction: `we provide the formal specification and ask the LLM to generate a proof script that is accepted by HOL Light within a fixed proof-check timeout.`
- Baseline restrictions: `restricted read-only sandbox with shell access, databases, and web search disabled`; `Zero-shot, query-only assessment`; `Each mode produces one answer per problem.`
- Full high-effort table: generic `66/562` (`11.7%`); bit-vector `27/311` (`8.7%`); program-state `28/552` (`5.1%`); functional correctness ARM `0/437`, x86 `0/422`. Thus the headline is dominated by non-routine-correctness lemmas. This is arithmetic from the published table, not a fresh experiment.
- Syntax attrition: `medium-effort run produced 743 answers that passed syntax checking and reached proof execution, while the high-effort run produced 766; the remaining answers were excluded at the syntax-check stage because they did not compile as valid OCaml/HOL Light tactic expressions.`
- Scope caveat, authors' own: `We treat this as an initial baseline rather than an exhaustive estimate of current model capability`.

Inference: the result tests a particularly unassisted HOL Light interface; it cannot distinguish intrinsic ISA-reasoning difficulty from missing context/API/syntax/feedback. It establishes no failure ceiling for a repository-using Lean agent.

### Theorem / Anthropic — reported scale + pinned public-scope correction

Source: https://www.anthropic.com/research/formal-verification.

- Source-reported scale: `Over the span of a few weeks, Claude successfully patched the bugs it found and then proved that there are no crashes on any input (up to 64 MB) for 239 entry points across 123 different OSS-Fuzz libraries.`
- Proof volume: `about 180 million lines of Rocq, with a typical proof running to about 600,000 lines` / `median length of 18,000 RISC-V instructions`.
- Quantifier/boundary: `every input less than 64 MB and every modeled Linux operating system (OS) response and memory layout` / `single-threaded static binary with a fixed memory budget on a RISC-V CPU using Linux OS`.
- **LZO scope conflict:** main post says `the result is the same as the original` and calls it a round-trip proof. But [pinned public README](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/README.md) explicitly says: `ONLY THE LENGTH is compared: the decompressed content is never memcmp'd against the input, so a decoder that returned the right number of wrong bytes would pass`. The [appendix p.6](https://www-cdn.anthropic.com/files/4zrzovbb/website/6867eadf760258fa8b42a504600cd3c036d16358.pdf) source snippet checks only `assert(r == LZO_E_OK && decompressed_len == size);`, conditional on `compressed_len < size`. Therefore full *content* round-trip correctness is **unconfirmed**; it would require an intermediate theorem not implied by these assertions. Do not silently infer it from no-crash/halts.
- No all-target solve rate inferable from the main post: it says `specifications for other fuzz tests we were not able to prove` but supplies no attempted denominator there. [Pinned public README:8](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/README.md#L8) exposes a **subset**: `61 entry points in 26 libraries have proofs`. Its full statement index includes unattempted/open goals, so proved/indexed is not an agent solve rate.
- **LZO availability check:** pinned target [README](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/projects/lzo/lzo_compress_target/README.md) lists every target statement `open`; full pinned [index/statements.tsv](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/index/statements.tsv) independently yields `target_rows=13 open=13`, awk rc 0. Positive control = header `id kind builds reading exits status detail revision fingerprint proof` (tab-separated), plus 13 matched rows. Thus no public proof for this target was located in this release; unpublished stronger intermediate work remains possible.
- **LZO source confirmed:** [source:85–100](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/projects/lzo/lzo_compress_target/source/lzo_compress_target.c#L85-L100): early return under `if (compressed_len >= size)`; final assertion `assert(r == LZO_E_OK && decompressed_len == size);`. Complete harness source inspected, not theorem replay. It also clamps large inputs with `if (size > (1 << 20))` / `size = 1 << 20;` ([source:45–46](https://github.com/theorem-labs/oss-verify-proofs/blob/a6839bb9e433b34c0d0710df5280194528877139/projects/lzo/lzo_compress_target/source/lzo_compress_target.c#L45-L46)), so the fuzz driver's process-input bound is not the amount of data this target compresses.
- Scope warning: `ASan doesn’t detect all memory safety bugs` / `the whole library wouldn’t be covered by verifying all entry points`.
- x86 Linux zlib RFC 1950 claim is also reported: `Claude directly proved the x86-compiled binary using Claude-generated (and heavily tested) formal semantics of the x86 ISA.` Artifact/independent replay not yet confirmed; do not count it as audited evidence.

### riscv-decomp — agent-friendly interface hypothesis, not measured agent evidence

Pinned repo = `0261343853e3a4e1ca189255c17092ff3eb81942`; exact files fetched/rematched, no replay.

- [SumDown.lean:13–26](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/SumDown.lean#L13-L26): `no leaf is framed, no block is composed, no loop rule is applied by hand` / user proves `two equations read off it` then `an ordinary induction on the counter`; `The two equations are still written by hand from the emitted function`.
- Exemplar scale, [same:6](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/SumDown.lean#L6): `Four instructions`.
- [Cert.lean:389–394](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/Cert.lean#L389-L394): `emitBody_sound` requires `(h : RunsTo body (fun _ => True) n x y)` before concluding `cpsTotal ...`. Emission soundness does not automatically establish the user-level total-correctness result; the run/induction proof remains.
- [Body.lean:35–44](https://github.com/dhsorens/riscv-decomp/blob/0261343853e3a4e1ca189255c17092ff3eb81942/Decomp/Extract/Body.lean#L35-L44): `Registers only` / `Loads, stores ... a call ... are out` / `One loop, no nesting`.
- **None-found measurement:** no autonomous-agent solve rate/time or A/B/C comparison in these inspected files; web queries for LLM decompilation surfaced this infrastructure, not an empirical comparison. This supports a *candidate interface* (agents prove ordinary recursive-function properties while certified tooling handles execution), not a demonstrated decoder-ready implementation.

### Talos — relevant Wasm WP precedent, **none-found agent performance measurement**

Pinned repo = `80644390de3ad4db3055445259a034413ae41577`.

- [README:29–31](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/README.md#L29-L31): `Proofs in Talos are built on weakest precondition (WP) calculus` / `without re-unfolding the interpreter at every step`.
- [NumIntegerOpt3/Spec.lean:155–158](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Spec.lean#L155-L158): `Partial-correctness loop invariant for the generated subtract-and-halve kernel` / `Löb induction is sufficient`.
- [same:889–901](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Spec.lean#L889-L901): `∀ input : Input, ∃ output : Output, Runs "gcd_u64" (args input) (result output) ∧ output.toNat = Nat.gcd input.left.toNat input.right.toNat`; theorem `gcd_u64_correct : GcdU64Spec` applies `mod3_gcd_smallStep_total`. Line breaks omitted from displayed signature; exact file inspected, not replayed.
- [CONTRIBUTING.md:80](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/CONTRIBUTING.md#L80): `If you used AI tooling to write or review code, say so in the PR description`. This and the repo's Codex/Claude instructions establish intended AI tooling use, **not** a measured autonomous success claim.
- Search coverage for agent result: pinned README, CONTRIBUTING, AGENTS, Claude Lean-LSP skill, optimized gcd proof; WebSearch `Talos Wasm Lean "agent" cajal`, `"Talos" "cajal-technologies" "proof" "AI"`; no published per-method solve rate/time found. Do not invent one.

### AWS LNSym — infrastructure, not itself an AI-agent success study

- [pinned README](https://github.com/leanprover/LNSym/blob/5c05220ff970e3bdd7813ad0c9ef3741522c8b92/README.md#L4): `LNSym is a symbolic simulator for Armv8 machine-code programs.`
- [AWS primary overview](https://www.amazon.science/blog/how-the-lean-language-brings-math-to-coding-and-coding-to-math): `aims to reduce the cost of verifying cryptographic routines, particularly block ciphers and secure hashes`; its AILean discussion concerns formal mathematics, not a published LNSym agent solve rate.
- **Firsthand negative scaling anecdote**, [Adam Langley](https://www.imperialviolet.org/2026/07/26/zstd-lean.html), “Aside: verified assembly”: `I put some (mostly LLM) time into trying this` / `small popcount example from the repo uses bv_decide ... requires more memory than my system has` / `Tiny functions do work` / `I, and a few LLMs, couldn't get it to scale any further`.
- Limits: code not published by author (`I'm not publishing the code`); no pinned LNSym rev, hardware/RAM, models, attempt denominator or matched interface control stated. Treat as a bottleneck lead, not a predictive failure rate. Also FVA excludes the current `bv_decide` auxiliary axiom path, so this exact discharge is not an automatically acceptable FVA tactic.
- `none-found`: no primary AWS LNSym autonomous-agent success-rate study in the pinned README, AWS overview, and searches `AWS "Lean" "symbolic" "AI" verification`, `Lean symbolic execution agents LNSym 2026 AWS machine code`, `"LNSym" "LLM"`. These queries do find source-level Aeneas/SymCrypt work, recorded separately rather than mislabeled AWS compiled-code evidence.

## R4.2 — Loop invariants / function contracts

### AutoVerus — task decomposition + specialized repair, not raw stepping

Source: https://arxiv.org/html/2409.13082, §6–8. Verus annotations over Rust source; SMT discharge, not a small-kernel binary proof chain.

- Contract held fixed: `provided with the Rust implementation and specification, AutoVerus is able to generate proof annotations`.
- Workflow: `preliminary proof generation, proof refinement guided by generic tips, and proof debugging guided by verification errors`.
- Budget qualification: `we report the number of correctly verified tasks after running AutoVerus (the whole three phases) for three times`; `122 tasks in its first attempt, with 10 more proved in its second attempt and 5 more on its third attempt`.
- Overall + loop-specific: `137 out of 150 (91.3%)`; Table 2 Diffy row `38 ... 38 ... 26 ... 12 ... 0 ... 5`; `Since the Diffy benchmark focuses on loop invariants, all the tasks from Diffy are handled by AutoVerus in the first two phases.`
- Feedback is deliberately typed: Table 3 `InvFailFront ... 131 ... 84 ... 64.1%`, `InvFailEnd ... 85 ... 78 ... 91.8%`; these are *repair attempts reducing errors*, not independent theorem success rates.
- Anti-cheating guard: `Lynette ... at the AST level` checks `can be compiled to the same executable`; `2,637 proof candidates, of which as many as 326 (12.4%) are unsafe. Fortunately, they are filtered out by our Lynette tool.` “Unsafe” here = changed executable/spec or other prohibited proof edits, not a C memory-safety judgment.
- Proof verbosity: `on the Diffy benchmark, AutoVerus generated an average of 22.2 loop invariants per task, 9.6 of which were unnecessary`; authors remove invariants mechanically when verification remains green. A passing proof is not automatically minimal/maintainable.
- Generalization limit: `It cannot represent many real-world proof tasks in large system code`.

### DafnyBench — feedback helps but does not solve long tasks automatically

Source: https://arxiv.org/html/2406.08467, §3–5.

- Task: `removed all of its hints (i.e., all of the assert and invariant statements in the body of the code)` and asked LLMs to fill them back.
- Protocol: `max_tokens =4096`; `up to n=10 attempts`; failures receive `the Dafny error message`.
- Published table: `Claude 3 Opus ... 67.8 ± 1.7`; `No LLM ... 26.9`; `best models succeeded on the first try about 54%`.
- Long-context association, not isolated cause: `success rate drops with program size` / `success rate drops with the hint quantity`.
- Scope: `programs each fit in a single file, avoiding the intricacies associated with distributed files or the integration of external libraries`.

### Aeneas/Hax experience report — pure model still needs invariant design

Source: https://arxiv.org/html/2605.30106v1, §2–5, §7.

- Extraction interface: `Rust loops become recursive functions with termination obligations`; `Aeneas relieves the proof engineer of memory-based reasoning`.
- Small empirical base, authors explicit: `two theorems that Aleph closed (PR #1 and PR #3), plus informal experiments on neighbouring lemmas`.
- Good fit: `Control-flow and structural lemmas` / `Linear arithmetic with mild side conditions` / `simp-closeable boilerplate`.
- Counterevidence to “model solves the hard part”: `Loop invariants on Aeneas-extracted recursive functions. We did not observe AI provers bypassing the inherent difficulty of finding the right invariant, so this remained a manual task in our work.`
- Broader boundary: a workaround is `rewriting the function as an extraction-friendly model`; that verifies the model unless its correspondence to the unchanged production artifact is independently proved. Do not silently count that workaround as FVA's no-rewrite link.

### SymCrypt/Aeneas — large positive follow-on with purpose-built proof interface

Source: https://arxiv.org/html/2609.15648v1, §5, §8.

- `Agents autonomously write formal proofs` / `∼5.1k theorems for a total of 125 KLOC of proofs, excluding theorem statements and auxiliary definitions`.
- Seven-hard-proof benchmark: `Opus 5 ... the only model that closes all 7 proofs within single sessions`; bars average `successful terminal runs` (selection caveat for latency/cost; no matched raw-Wasm comparison).
- Explicitly declines longitudinal causal productivity claim: `We report on our experience but do not attempt to quantify productivity benefits, since the toolchain and agents significantly evolved throughout our project.`
- Source-to-pure-model + contracts is the interface, not compiled-byte verification. Details under R4.5.

## R4.3 — Large agent developments

### Certora CLean zlib

Source: https://www.certora.com/blog/formally-verifying-zlib-memory-safety-with-lean.

- Architecture: `CLean extends it to emit Lean4 instead, and pairs the exported AST with a Lean port of CompCert's Clight semantics plus a separation logic to reason about it.`
- Seven-loop mathematical seam: `building a small combinatorial model of the function (counts, offsets, live symbols) as pure mathematics independent of the program, about 1,600 lines of it, and then showing the loop maintains the correspondence`.
- Hardest invariant: `tracking the Huffman code being built in bit-reversed form and relating zlib's left variable to the unused code space, that is the Kraft inequality as a loop invariant.`
- Human role + maintainability limit: `humans wrote next to none of the 20,000 lines; our work was reviewing the theorem statement, the assumptions, and the main memory-safety proof` / `Much of what a human still does here (proposing invariants, drafting specifications, assembling proofs) is exactly the kind of work we are now working to automate end to end.`
- Reported effort + replay: `The entire proof of concept described here took about two weeks: the C-to-Lean tool, the semantics, the program logic, and the finished memory-safety proof` / `the proof itself rechecks in 29 seconds`.
- Exact scope limit: `the theorem we proved is about memory safety and termination, not (yet) functional correctness` / `the proof is about the Clight representation of the C source, not about compiled machine code` / `our Lean development does not connect to` CompCert's compiler theorem.
- Trust boundary: `the development carries two axioms mirroring CompCert's own treatment of external functions and inline assembly, plus their determinism. inflate_table calls no external function, so none of them is exercised by this proof.` No independent dependency-closure audit performed.

### Mesh intersection — milestones + informal proof planning, but debt remains

Pinned repo = `c537025f69511110108acc9608dc1cdb19025057`.

- [README:5](https://github.com/schildep/verified-3d-mesh-intersection/blob/c537025f69511110108acc9608dc1cdb19025057/README.md#L5): `over 60,000 lines of Lean proofs` / `I guided the agent through the milestones`.
- [README:58–72](https://github.com/schildep/verified-3d-mesh-intersection/blob/c537025f69511110108acc9608dc1cdb19025057/README.md#L58-L72): `stepwise refinement allowed me to delegate large pieces of work to agents` / `first write informal proofs before formalizing` / `Some of the above steps took over 24 hours of autonomous agent work`.
- [CLAUDE.md:116–145](https://github.com/schildep/verified-3d-mesh-intersection/blob/c537025f69511110108acc9608dc1cdb19025057/CLAUDE.md#L116-L145): `Prover and implementation agents never modify the specification files` / `write an informal but mathematically rigorous proof` / `start a review agent that reviews the informal proof` / `Only then should the prover agents start writing the lean proof`.
- [CLAUDE.md:153–180](https://github.com/schildep/verified-3d-mesh-intersection/blob/c537025f69511110108acc9608dc1cdb19025057/CLAUDE.md#L153-L180): `The LSP keeps the file loaded and re-elaborates incrementally` / `lean_multi_attempt (try several tactics at a position without editing)` / `The cold build is the only completion gate`.
- **Maintainability caveat, author's own:** [README:76](https://github.com/schildep/verified-3d-mesh-intersection/blob/c537025f69511110108acc9608dc1cdb19025057/README.md#L76): `both the implementation and the proofs ... are nowhere near as clean and do not follow a cohesive design`.
- Boundary: proofs concern Lean implementation; ordinary compiler/runtime path is not independently kernel-verified. This example demonstrates controlled review surface + autonomous formal development, not a compiled foreign-code link.

### lean-zip — simple reference + optimized refinement under a proof ratchet

Pinned repo = `2f7a63f38195bc667a926881b55d10c9f8a88eeb`.

- [README:20–30](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/README.md#L20-L30): `more than 1,100 theorems across ~32k lines of proof` / `entirely by loosely supervised AIs: coding agents claimed issues, worked in their own git worktrees, and opened pull requests that could not merge unless the round-trip proof still went through`.
- [`.claude/CLAUDE.md:33–52`](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/.claude/CLAUDE.md#L33-L52): `proving the optimized version equal to the simple one` / `For optimized variants, the spec is equivalence with the simple version` / `Do NOT weaken a theorem statement just to make a proof easier`.
- [same:55–65](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/.claude/CLAUDE.md#L55-L65): `Do NOT write multi-line tactic blocks without checking intermediate state`; exact multiline source excerpt:
  ```text
  - Loop constructs from `while` / `for ... in [:n]` produce opaque `loop✝`
    functions that cannot be unfolded in proofs — use well-founded recursion
    with `termination_by` when you need to prove through a loop
  ```
- [README:171–177](https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/README.md#L171-L177): `four small stopgap primitives` / `proofs are about the reference bodies, and the C is trusted to match them`.
- Scope: round-trip = encoder-produced streams, not arbitrary-input decoder acceptance theorem. Native runtime and C replacements remain a trust boundary. No benchmark compared this workflow with proving an unchanged C decoder's compiled bytes.

## R4.4 — Friction / mitigations

### FVA local bench evidence (post-hoc, not causal)

Source: `/home/eturkes/Projects/fva/.agent/archive/maintain-bench-direction.md:18,27–31`.

- Agent usability: `30/30 unaided from AGENT.md; ≈ 20–40 % context on FVA internals; wasm_step1 failed on T7; no MCP/skill (D6)`.
- Attribution limit: `Overhead analysis (post-hoc, indicative)` / `No causal fraction of the token gap identified`.
- Orientation is not just debugging: `≈ half the internal reads precede the first failed build (orientation, not only tactic debugging)`.

### Proof reuse (Theorem source-reported experiment)

Source: https://www.anthropic.com/research/formal-verification, “Proofs can be reused”.

- `When given access to this shared workspace, agents needed 17% fewer tokens than when they worked alone, and some agents even succeeded after previously failing in a solo attempt.`
- `Most of a proof concerns code that every program contains (particularly initialization of the C runtime and AddressSanitizer)`.
- Boundaries: no experiment code, raw token totals, randomization, variance, or confidence interval inspected yet; treat as an attributed intervention result, not independent causal estimate for FVA.

### Binary proof expert appraisal — models arise, but abstraction does not arrive reliably

Source: [Anthropic appendix pp.4–5](https://www-cdn.anthropic.com/files/4zrzovbb/website/6867eadf760258fa8b42a504600cd3c036d16358.pdf), inspected all six pages.

- Model/refinement pattern: `Almost universally, agents first formulated a short specification describing what outputs a program ... can produce, and then proved that both programs match that specification`.
- Repetition: `repeatedly spelling out details about the program's execution` / `specifying the contents of CPU registers` / `explicitly writing out integer conversions` / `explicitly spelling out that many different addresses are all distinct`.
- Agents sometimes discover framing/calling/allocator abstractions, but `not every agent used these techniques` / `correlated with only a modest reduction in proof size`.
- Scaling caveat: `it remains to be seen whether agents can scale this verbose proof style directly to more complex programs`; points to MachCSL's complexity wall, not a controlled ablation.
- Generated-code caveat: `Over half of each proof is machine-emitted by tools Claude wrote for itself (instruction encodings, lookup tables)`; headline line count is not all handwritten creative proof effort.

### MachCSL — compiled-code abstraction intervention

Source: https://arxiv.org/html/2609.04043v1, §7; page text inspected via BrowserOS Neo + webtext.

- Failure: `agents are not at all good at ... introducing appropriate abstractions`; file-system proofs `involved direct reasoning about the contents of on-disk blocks` and became `extremely verbose and fragile`.
- Intervention/outcome: `We forced the agent to introduce abstract state capturing the notion of an inode, a directory, and a file system tree` / `allowed the agent to finish the proofs, whereas before this abstraction, it could not scale`.
- Contract interface: `once a function is stated with a clear separation-logic spec, and clear invariants owning separation-logic facts about shared resources, agents are effective at doing the actual proofs`.
- Failure spiral: `continuing to introduce more lemmas, theorems, specs, case analyses, etc., without really making progress`; remedy = `stopping the agent, discarding its work, and starting over with a more precise goal statement`.
- Maintainability: per-function `SpecF.v`, `CodeF.v`, `ProofF.v`, `LinkF.v`; `top-level adequacy theorem cancels out all of the intermediate specs` and enforces compositional compatibility. This is particularly relevant to keeping FVA proof-side models/invariants outside the human-review closure.
- Tooling: `cached the state of rocq repl ... incrementally re-checked a modified file by rewinding ... to the common prefix`.
- No quantitative causal effect established for these interventions; expert experience, in one large compiled-kernel project. Concurrency/OS complexity is unlike LZ4, but ABI/memory/function abstraction failure mode transfers plausibly.

## R4.5 — Agent-oriented candidate

**Candidate = contract-first proof-producing VC/WP interface, with untrusted agents searching for invariants + helper lemmas and all semantic glue rechecked by Lean.** Orthogonal to A/B/C; no evidence establishes a magic fourth semantic route. In FVA, this would still be proved sound against the existing Wasm small-step semantics + access trace + termination claim.

Strong primary engineering evidence: https://arxiv.org/html/2609.15648v1, §5.2–5.6.

1. **Contract lookup instead of callee unfolding:** `the theorem is marked with a @[step] attribute, to save it in a database of code properties, so that proofs of functions that call reduce can use it as a lemma without having to unfold its definition`.
2. **Mechanical control-flow, mathematical residue:** `step* leaves three arithmetic goals to be proved` / `purely in terms of integer arithmetic`.
3. **Fast, bounded automation + state reuse:** `we aim for grind to fail fast when a goal cannot be closed` / `carefully thread the state accumulated by grind to avoid repeatedly deriving the same facts`.
4. **Proof-producing reshaping without source rewrite:** `decompose ... automatically fold selected code parts into auxiliary function calls` / `a theorem that proves the transformations preserve functional equality` / `the command and its use are outside the verification TCB`.
5. **Agent-guided use:** `effectively used by agents, which are instructed to apply it on large code ... as well as code whose monolithic proof turns out to be too complex to automate`.
6. **Scaffold before proving:** `writing a theorem statement for every Rust function, as well as pre- and post-conditions, and loop invariants; all proofs are admitted at this stage—the goal is to prevent backtracking ... because a precondition is missing`; API review then proof completion. Admitted scaffolds are planning artifacts, not final verified output.
7. **Immutable semantic boundary:** `agents cannot edit specifications, axioms, and implementations during proof development: this requires escalation and explicit human approval`.

Transfer hypothesis: expose small, compositional verified contracts (`memcpy`, `memmove`, forward-overlap copy, read-extension, guarded wildcopy); mechanically reduce Wasm blocks/calls to proof obligations over slices, offsets and a declarative LZ4 relation; give agents minimal goals, statement search + warm incremental feedback. This is not evidence that pure decompilation already works for optimized LZ4, and buffer footprints/termination must be preserved explicitly (functional equality alone is insufficient for FVA R1).

## R4.6 — Closest decoder/copy agent case: liblzma with VST

Source: https://arxiv.org/html/2608.29716v1, “Agent-Driven Verification of Memory Safety for liblzma Decoder Components with VST”.

### Proof interface + demonstrated scope

- Model/spec split (§3.1): `A functional Model gives executable Rocq definitions of a routine's abstract state and transition` / `A Spec then adds VST representation predicates that relate those values to C structs and buffers` / `postcondition requires the C outcome to agree with the model` / `Proof agents then discharge ... by symbolic execution and entailment solving`.
- Human semantic gate (§3.1): `Humans review and approve the models and funspecs`; agents report candidate refinements rather than silently applying them.
- Closed-body inventory (§6.2): `27 closed body theorems: 22 within the decoder scope and five supporting common-layer bodies`; table columns `Name | Spec | Proof | C`: `lzma_bufcpy | 96 | 392 | 18`, `dict_repeat | 31 | 2,081 | 47`, `dict_write | 55 | 2,811 | 13`. Relevant real buffer/overlapping-repeat contracts, not merely mathematical sort benchmarks. These are source-reported SLoC, not measurements rerun here.
- Largest body: `lzma_decode | 76 | 183,268 | 338`; macro-expanded Clight source contains many repeated paths. Do not extrapolate a source-line ratio to FVA Wasm instruction count.
- Important boundary (§6.4): `For the transformed verified-xz snapshot` / `applying the result to upstream liblzma additionally requires source equivalence`.
- Imported-contract closure (§6.2): `outer module imports ... VST's memcpy_spec`; allocator body lemmas are `Rocq Parameters`, memory-manager predicate introduced by `an axiom (mem_mgr_rep)`; placeholder `lz_decoder_end_placeholder_spec` remains. A body proof under such hypotheses ≠ closed whole-library proof.
- Termination/semantics (§2.1): `Clight safety and model-relative partial functional correctness`; theorems are not FVA's R1–R3 full all-input compiled artifact theorem.

### What actually slows the agent

- §3.2: `naive loop of editing a file and re-running coqc is unworkable`; one file `hours and up to 20 GB of RAM`.
- Warm tools: `rocq_get_state`, `rocq_query`, speculative `rocq_step`, incremental `rocq_compile_lsp` `up to a given position`; saved checked snapshots reload `in seconds` (source report).
- Agent-sized goal extraction: `rocq_extract ... mechanically cuts a subgoal out of the live proof`; generated fully elaborated definitions `can exceed 100,000 lines`; `agents are told to treat it as opaque and work only against the Lemma skeleton`; final use is an ordinary kernel-checked lemma application.
- Context firewall (§3.2 hooks): `denies reading or editing the ~100k-line autogenerated goal files (which only burn context)` (the source uses a rendered mathematical approximation sign; sense unchanged).
- Key proof-size result (§6.2): `Symbolic execution itself is a minor cost: only about 2% of the lines in the 28 extracted proofs are forward steps`; `Roughly 42% ... blocks repeated verbatim`; `18-conjunct decoder-state well-formedness argument, written out 63 times`.
- Contract reuse contrast: `lzma2_decode ... delegates LZMA1 decoding to a function with a VST specification. Its proof handles that call with one forward_call`.
- Profiling (§3.3): targeted rewrites, explicit pure facts + controlled one-step unfolding `reduced individual tactic calls from 40 s or more to under a second without changing what was proved`; avoid reducing a whole model, not just whole machine semantics.
- Scale, not productivity estimate (§6.3): `1,595 agent sessions over the 70-day lzma_decode development interval`; `figures characterize scale and observed outcomes, not human effort or labor savings; no human-only baseline is available`.

Inference for FVA: reduce repetitive invariant restoration with typed local summaries and representation lemmas; keep generated states opaque and expose small residual mathematical goals. A functional model by itself does not prevent context/proof blow-up; the *representation and proof API* determine what the agent must repeatedly manipulate.

## R4.5 supplement — residual VCs must be *agent-sized*, not merely generated

### NTP4VC: a caution against raw VC dumping

Source: https://arxiv.org/html/2601.18944v2, §4–5. Benchmark VCs from Why3/Frama-C, with analogous Lean/Rocq/Isabelle tasks; not a compiled-code benchmark.

- Corpus: `600 VCs` selected from `over 7.5k VCs`; model prompt `zero-shot ... only the problem statement and ... definitions and previously proved lemmas`.
- Table 5, Lean: DeepSeek-Prover-V2-671B `1.67` P@1, `3.00` P@8 (percent); DeepSeek-V3.1 `0.50` P@1, `1.67` P@8. These are query-only baselines, not current tool-using frontier agents.
- Authors' broad statement: `all NTP models fail to achieve pass@8 scores above 12%` across the three assistants.
- Mechanism: `VCs are often long, deeply-nested, machine-generated formulas` / `extreme demands on a model's ability to maintain long-range syntactic coherence`.
- Important distinction: `annotation generation ... decompose hard VCs into simpler subgoals` and VC proving `can be applied orthogonally`.

Inference: a raw enormous formula is not a helpful abstraction boundary; canonical names, compact invariants, reusable lemmas, residual-goal splitting + interactive checking remain necessary even after decompilation/VC generation.

### PV-Bench/QCP: useful interface pattern, **not** a kernel-verified drop-in

Pinned [README](https://github.com/QinxiangCao/PV-bench/blob/39d9c0dc7bd7beafb26024a81ceadc448f1fbfe0/README.md).

- `QCP ... symbolic execution and separation logic` / `automatically discharges verification conditions where possible and exports the remaining obligations to Rocq or Lean 4`.
- Staged tasks = specs, invariants/helper contracts, residual proofs. Table T2: `with the code and spec left byte-for-byte unchanged`; T3: `manual proofs that are left`.
- Critical trust qualification: `released automatic results use Admitted / sorry without exported proof certificates; they are not independently rechecked by the proof-assistant kernel`.
- No model success-rate evaluation read in this README. Count it as an interface example + trust warning, not measured evidence of a fourth method outperforming A/B/C or a library recommendation for FVA.

## Coverage / limits

- **No matched A/B/C experiment found.** Places searched = arXiv/ICLR/author/vendor primary pages; AWS/LNSym, Talos, Theorem public docs + selected pinned proof files; FVA local archive. Query families included `s2n-bignum-bench 2603.14628 agents binary verification LZO theorem Anthropic`, `LLM formal binary verification benchmark symbolic execution refinement decompilation agents Lean Rocq`, `LLM "decompilation" "proof" "Lean" verification agent`, `"binary verification" "agents" "refinement"`, `"agent" "symbolic execution" "proofs" "invariants" "Lean" compilation`, plus the AWS/Talos queries listed above. Broader late queries returned known projects, reverse-engineering/testing rather than formal proofs, or unquantified infrastructure. This is a bounded search result, not a proof of nonexistence.
- **No per-method copy/parser/decoder solve-rate comparison found.** Searches included `LLM loop invariants "memcpy" verification Lean agent`, `"LLM" "memmove" "proof"`, `"LLM" "loop invariants" "decoder" formal verification`, `"symbolic" "Lean" "agent" "memcpy" proof`. Positive concrete decoder/copy body evidence = liblzma/VST; parser/binary corpus evidence = Theorem; invariant benchmark evidence = AutoVerus/DafnyBench. These differ in model, budget, task size, trust and link, so a rate comparison would be confounded.
- **Unconfirmed claims:** full-content LZO round trip; unpublished x86 Linux zlib proof artifact; autonomous Talos solve rate; AWS LNSym agent benchmark. Named places inspected are recorded in R4.1. None treated as established performance evidence.
- **Sampling:** Theorem corpus not fully inspected; direct samples = public README/origin/proving/exploring docs, full statement index, LZO target/source, and fast_float `lib/FF/Bigint_shl.v` (pinned a6839bb); only the full index supports the LZO status count. No claim of all-proofs axiom audit or absence of stronger intermediate theorems. Talos sampled optimized-gcd theorem + framework/agent docs; no exhaustive project scan. LNSym README + AWS overview + firsthand anecdote, not the entire proof tree.
- **Checks performed:** raw source pins obtained via GitHub API; mesh/zip/Talos clones read only; LZO source inspected at exact lines, statement-index rows counted with positive header control; Anthropic appendix all six pages visually inspected + extracted; final seeded-row validator below. No `lake`/`lean` invocation, upstream proof replay, FVA gate, semantic test, benchmark rerun, downloaded-code execution, or state-changing git command.
- **Cleanup:** downloaded research artifacts/clones in `/tmp/u19c2-researcher-4` removed at close; durable evidence = remote pinned URLs + excerpts in this report. Own BrowserOS Neo source tabs remain available for inspection. Local FVA archive evidence read at HEAD `e5de229ded1e512e7da5996a5d4f0cb782b8a9a6`.

## Sources

- [s2n-bignum-bench v2](https://arxiv.org/html/2603.14628v2)
- [Anthropic binary verification](https://www.anthropic.com/research/formal-verification), [six-page appendix](https://www-cdn.anthropic.com/files/4zrzovbb/website/6867eadf760258fa8b42a504600cd3c036d16358.pdf)
- [Theorem pinned public proof release](https://github.com/theorem-labs/oss-verify-proofs/tree/a6839bb9e433b34c0d0710df5280194528877139), [roadmap/microbenchmark scope](https://theorem.dev/blog/verified-software-stack/)
- [MachCSL](https://arxiv.org/html/2609.04043v1)
- [liblzma/VST agent development](https://arxiv.org/html/2608.29716v1)
- [AutoVerus](https://arxiv.org/html/2409.13082), [DafnyBench](https://arxiv.org/html/2406.08467)
- [Aeneas/Hax AI-prover experience report](https://arxiv.org/html/2605.30106v1), [SymCrypt/Aeneas](https://arxiv.org/html/2609.15648v1)
- [CLean zlib](https://www.certora.com/blog/formally-verifying-zlib-memory-safety-with-lean)
- [mesh c537025](https://github.com/schildep/verified-3d-mesh-intersection/tree/c537025f69511110108acc9608dc1cdb19025057), [lean-zip 2f7a63f](https://github.com/kim-em/lean-zip/tree/2f7a63f38195bc667a926881b55d10c9f8a88eeb)
- [Talos 8064439](https://github.com/cajal-technologies/talos/tree/80644390de3ad4db3055445259a034413ae41577), [LNSym 5c05220](https://github.com/leanprover/LNSym/tree/5c05220ff970e3bdd7813ad0c9ef3741522c8b92), [AWS overview](https://www.amazon.science/blog/how-the-lean-language-brings-math-to-coding-and-coding-to-math), [Langley firsthand experiment](https://www.imperialviolet.org/2026/07/26/zstd-lean.html)
- [NTP4VC v2](https://arxiv.org/html/2601.18944v2), [PV-Bench 39d9c0d](https://github.com/QinxiangCao/PV-bench/tree/39d9c0dc7bd7beafb26024a81ceadc448f1fbfe0)
- [riscv-decomp 0261343](https://github.com/dhsorens/riscv-decomp/tree/0261343853e3a4e1ca189255c17092ff3eb81942)
- Local primary archive: `/home/eturkes/Projects/fva/.agent/archive/maintain-bench-direction.md:18,27–31`.

## Deliverable validation

- Top-level targets: `target_rows=6 expected_rows=6 malformed_rows=0`; structural validator rc 0.
- Required seeded-cell grep → `0`, rc 1 (grep's expected no-match status). Positive control containing one seeded cell → `1`, rc 0.
- Cleanup: `/tmp/u19c2-researcher-4` removal rc 0; absent-path test rc 0. Own saved browser text outputs removed, rc 0. No repo changes outside this deliverable.

researcher-4-DONE-1
