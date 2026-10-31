# U19 route log (frozen L1 + effort)

- L1 frozen: 2026-10-31T15:06:58+09:00 sha256 Ext.lean 3466d1aa31b66595, Code.lean 4b4bab1b8ef01fc9
- seam (setup, not route cost): Access spec/impl/proofs, Footprint lib (MustW, Until, wasm_cstepw/u, wasm_within), FootprintExamples, Lz4C Instance/Code/Ext
- route D start: 2026-10-31T15:06:58+09:00
- route D done: 2026-10-31T15:28:28+09:00 (ext_l1 proven; elab 6.09 s wall, 2.72 GB max RSS incl. imports; codeLines TBD)
- route R start: 2026-10-31T15:29:07+09:00 (shared helpers moved out of ExtDirect into ExtCommon: counted in D's M0, reused by R = S2 order effect)
- route R done: 2026-10-31T15:33:40+09:00 (ext_l1 proven; elab 5.94 s wall, 2.73 GB incl. imports)
- M4 structural delta (before repair): -O1 artifact 11,167 B (sha256 2268a91bc122168f…) vs 8,469 B; func 2 WAT 793 vs 583 lines; memcpy 38 vs 98, memmove 76 vs 200 lines (unrolling gone). Region: loop body 33 vs 22 static instruction nodes (an earlier "30" here is superseded); locals renumbered (18 = q = p+1 pre-incremented, 19 = acc, 4 = acc copy, 3 = q, 14 = lim, 20 = byte, 16/17 = out pointer/acc); read at q−1; both guards exit by `br 1` to the enclosing block with error flag −1 in local 17 (O2: `br 7` straight to @3); normal exit = explicit `br 2` (O2: fall-through). -O2 rebuild = byte-identical to the artifact (positive control).
- M4 repair order: R first, then D (reverse of build order).
- M4 shared binding start: 2026-10-31T15:36:37+09:00
- M4 shared binding done: 2026-10-31T15:39:17+09:00 (O1/Ext.lean sha256 aefcd9ddd5499a0b; includes the 6-vs-5 level path miscount fix)
- M4 repair R start: 2026-10-31T15:39:17+09:00
- M4 repair R done: 2026-10-31T15:46:39+09:00 (O1/ExtRefine: Sim/SimExit/sim_one/sim/ext_l1 new; extModel, ModelOK, model_ok reused unchanged)
- M4 repair D start: 2026-10-31T15:46:39+09:00 (borrows R's -O1 stepping script = order effect)
- M4 repair D done: 2026-10-31T15:49:51+09:00
