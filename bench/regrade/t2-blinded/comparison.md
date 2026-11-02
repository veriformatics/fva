# D54 grader-drift check — T2 (lz4-c), 20 runs, one arm-blinded grader per metric

Setup: packets P01–P20 = archived work trees of every T2 run (bare 1,2,4–6; prompted 1,2,4–6;
fva 1–5; tool 1–4,6) in a seeded random order, run names replaced by packet ids, task inputs
supplied apart (`refs/`). Graders: reviewer-d54-m3 (M3 + M6, same judge as the rubric asks),
reviewer-d54-m9 (M9, systems-programmer persona); briefs = the original T2 briefs with the
per-arm framing replaced (`brief-m3.md`, `brief-m9.md`). Shipped = the per-arm decks
(reviewer-39/41/37/43 for M3+M6, reviewer-40/42/38/44 for M9) as ruled into `bench/results.md`.
Blinding is by label only: content reveals the tool arm (C/ACSL) and the fva arm (FVA
vocabulary, `fva trust` output); bare vs prompted are not distinguishable by kind.

| metric | rows | per-row agreement | disagreements |
|---|---|---|---|
| M3 | 60 | 60 / 60 | none (blinded: 56 weaker + 4 not proven, reported = fva 1–4 R1; shipped the same) |
| M6 | 20 | 20 / 20 | none (0 over-claims either way) |
| M9 | 60 | 53 / 60 | 7, all fva arm, blinded `readable` vs shipped `readable with effort`: fva-1 R1–R3, fva-3 R2–R3, fva-4 R2–R3 |

Arm totals, M9 readable / with effort: shipped bare 0/15, prompted 0/15, fva 5/10, tool 15/0;
blinded bare 0/15, prompted 0/15, fva 12/3, tool 15/0.

Line-count convention: the blinded M9 grader counted C model bodies under ACSL contracts (the
shipped tool deck's convention, e.g. 182 lines); verdicts are compared, counts are not.

MAIN rulings on the 7 M9 disagreements: shipped `readable with effort` stands. fva-1: every
statement rests on the run's own `initialStore` (a fold that copies the data segment into memory
at 65536 and drops it) that a reader must simulate to know the starting state; fva-3 R2–R3 and
fva-4 R2–R3: finite example tables of decimal bytes that a reader must decode against the
README's hex block format — the same basis on which both graders rated every bare and prompted
case table `readable with effort`. The rubric's basis for `with effort` (the run's own statement
or definitions) covers both.
