# MAINTAIN — bench v2 outcome + direction (closed; direction decision open)

Request: summarize the bench v2 outcome, conclude, recommend where FVA goes. Delivered in chat; this file = the durable record. Direction = unruled (user paused it for the `fvtrace` session's formal-verification-API context).

## Conclusion (MAIN; claims appraised by scientist-1 on the results, scientist-2 on C1–C5)

- Productivity = no: fva 3.0–11.5× bare total input tokens (1.3–3.9× uncached, 1.3–1.9× output; no dollar cost measured), 1.5–3.5× prompted; bug discovery parity (every arm found every known defect; no arm falsely verified) ⇒ neither outcome sentence shown (`bench/results.md` summary).
- FVA's robust gain = link to the shipped bytes: M10 fva 30/30, bare 12/30, prompted 12/30, tool 4/15; other arms reached bytes on T2/T3 via run-written extractors + semantics (76–281 lines/run).
- Refutation evidence: for a deterministic defect an executed reproducer usually suffices; a proof adds composition, runtime-independent checking, coverage of every allowed nondeterministic outcome (scientist-2 C1 = overstated as "few need it"; no bench task needed it).
- Unshown where the thesis lives: all-input proofs at real size. Decoders `LZ4_decompress_safe` = wasm func 2 ≈ 581 body lines + callees ≈ 97 + 199; lz4_flex `lz4_decompress` = func 7 ≈ 981 (+ 54 in callees); largest FVA all-input proof ≈ 139 (edgeR `calc_cpm_raw`, D9). Binary-level proofs at this scale exist with heavy abstraction + expert automation (seL4 translation validation: 234/260 functions paired at `-O1`, 11,736-instruction binary, SMT-backed — Sewell, Myreen, Klein PLDI 2013; s2n-bignum: e.g. 1,675-instruction P-521 doubling in HOL Light); agents weak there (s2n-bignum-bench 2026, arXiv 2603.14628: GPT-5.3-Codex 5.3 % high effort, expert specs given) ⇒ gap in FVA, not a known wall.

## Intent goals vs bench evidence

| goal | evidence | verdict |
|---|---|---|
| one link, any language | one `fva lift` path: hand-written Wasm (T1), C (T2, T4 core), Rust (T3), C++ (T7), 30/30; R + Python = per-output certificates (T5); WASI, EH, WasmGC unsupported | shown, compiled languages |
| link to real implementation, no rewrite | every fva statement on unchanged bytes, `fva trust`-checked; not exclusive (T2/T3 own extractors) | shown |
| agent-usable (primary target) | 30/30 unaided from `AGENT.md`; ≈ 20–40 % context on FVA internals; `wasm_step1` failed on T7; no MCP/skill (D6) | feasible, costly (D55) |
| unbounded AI proofs behind a small spec | partial-domain proofs only on decoders; whole-domain = Verus models only | not shown at real size |
| small reviewed surface, measured | measured every run (medians 9–115); smallest Lean arm T2, T3, T7, tie T1, larger T4, T5; T2/T3 not at equal M3; base ≈ 2,200 code lines / 23 spec modules (approximate count, bench-v2.1) ⇒ break-even ≈ 5–9 T2/T3-like projects if read whole | partly shown |
| plain-English review | 0 `fva explain` invocations in 105 runs (control: 46 `fva lift`); no rubric metric | not tested (D56) |
| independent kernels + known-false proofs | fva 116/120 first-site cheats, prompted 117/120; real checker-bug canaries = gate, not bench | works, not a differentiator |
| verify the compiled artifact | statements 30/30; all-input at real size no | partly shown |
| certify outputs (compilers, generators, AI pipelines) | T5 certified 5/5, best M3 (6 faithful vs 2, 2); toy compiler in `FVATest` unbenched; AI pipelines none | shown for program outputs |
| any pre-existing project, find a path | single functions/outputs, prepared inputs; no whole-project run | not tested |

## Overhead analysis (post-hoc, indicative)

- Method: archived `bench/runs/*/stdout.jsonl.gz`; step = completed item (command | file change | message; not a model request); weight = chars (output capped at 35,000 ≈ gpt-6.1-sol 10k-token tool-output truncation, read from codex 0.166.0's catalog; 0.163.0 assumed equal) × later steps; categories by command-position regex; MAIN script = `.scratch/discuss/token-attr.py` (scratch, not regenerable from git), cross-checked by scientist-2's shell-token classifier (task-median discrepancy 1.2–5.9 % weighted volume; internal share T1 22 % vs 36 %).
- fva vs bare: steps 1.5–2.6×, input per step 1.1–3×; fva internal-source reads (`FVA/{Impl,Proof,Trust,Tool,Cli}`, scripts, lakefile) 11–19 steps/run ≈ 20–40 % of context volume; spec-vocabulary reads 4–13 %; waiting = 1–2 huge `ps` listings, not polling count; ≈ half the internal reads precede the first failed build (orientation, not only tactic debugging).
- No causal fraction of the token gap identified; the 2× rubric bound vs bare needs input cuts of 34–83 % by task (T7 83 %).

## Recommendation + options (unruled)

- Recommended: decoder feasibility spike (one MAINTAIN session): all-input proof of lz4 C `LZ4_decompress_safe` on its bytes vs T2's audited requirements; checkpoint 1 = one loop (match copy | length extension) with an access-tracking invariant, direct stepping vs refinement to a proof-side Lean model compared on it; checkpoint 2 = full theorem; refinement must preserve accesses, termination + every allowed outcome; model never imported by claims; stop = checkpoint 1 unproven within the session → record cause; record effort, proof/export size, replay time + memory, surface growth. Pass → IMPLEMENT proof scaling (D9 block summaries, D52, concrete-call → theorem command, D55 orientation) + bench v3 (held-out, FVA frozen, matched assurance targets); fail → source-level link (reverses the WASM-lift + Verus-rejected rulings; compiler + translation trusted) or a narrower claim.
- Alternatives: ergonomics first (D55 + D52, then an equal-assurance ablation); source-level pivot; pause. D56 (explain test) can ride along any.

## fvapi context (from the `fvtrace` session, MAIN fvtrace-c0)

- fvapi (user's idea, new private repo `~/Projects/fvapi`, PROTOTYPE next, endpoint host vflab): a private library behind an API that fvTrace, FVA + outside tools call; untrusted oracle, trusted checker: every answer = proof/certificate the client re-checks (Comparator-style: sandboxed build → export → kernel replay → statement match); no LLM at request time (subscription terms) ⇒ lookups + proved checkers + CPU automation; products = method checkers + reviewed specs, and proofs about specific artifact versions + expensive witnesses. For FVA: beside `lift`/`trust`/`certify`; `fva trust` on the client = the verdict. Sources: `~/Projects/fvtrace/.scratch/fvapi/{final,scientist-1,researcher-1..5}.md`, `~/Projects/veriformatics/business/product-direction/{README,vflab-setup}.md`.
- fvapi's scientist-1: "library cuts time + cost" = unsupported (hypothesis); this bench = its local anchor.
- FVA-side consequences (sent to fvtrace-c0): (1) `fva trust` is not yet a checker for untrusted packages — D12 (unsandboxed `lake build` of the project's lake config), D48 (Mathlib `.olean` contents trusted by `.git/HEAD`), D49 (base `.olean`s from the project's own build) ⇒ prerequisites for "fvapi delivers, `fva trust` decides"; a VM around the client shields the host (D12) but not the verdict (the package's build still rewrites `.olean`s inside it: D48, D49) (D58); an export-only delivery skips FVA's link + surface checks; (2) delivered `Lifted` modules = the artifact's bytes ⇒ licensing (D57); (3) the bench's orientation overhead (D55) = library-navigation cost ⇒ answer-shaped endpoints over agent-read libraries; (4) version proofs walk instruction lists ⇒ break per release; refinement localizes the re-proof to the simulation = what the decoder spike tests.
- Coordination: fvtrace-c0 reads (never writes) `FVATest/Subjects` (EdgerCpm, Tmm, GlmIround) + `FVA/Cert` for seed entries, pinned at `56a4537`.

Teammates: scientist-2 (scientist, astra lane) — C1 overstated, C2 friction supported / causal share unidentified, C3 overstated (decoder-size correction), C4 supported as a research route with constraints, C5 bounded spike endorsed; MAIN adopted every correction.
