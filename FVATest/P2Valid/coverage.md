# P′ validation suite coverage (tester-4, blind: contract U28c + SpecTec 2.1–2.4)

| rule | what | fixtures (file:line) | +valid | −invalid |
|---|---|---|---|---|
| V1.idx-range | source `idx x` valid iff `x < C.types.length` (heap types in value types, ref.null, call_ref, block types) | `types.wast:3`; `types.wast:5`; `types.wast:7`; `types.wast:9`; `types.wast:11`; `types.wast:77`; `types.wast:79` | 1 | 6 |
| V1.sub-null | `(ref ht)` ≤ `(ref null ht)`, never the reverse (operands, results, labels, globals, tables) | `types.wast:13`; `types.wast:15` | 1 | 1 |
| V1.sub-def-func | `(ref $t)` ≤ `(ref func)` / `funcref`; `funcref` ≰ `(ref null $t)` | `types.wast:17`; `types.wast:19`; `types.wast:21` | 2 | 1 |
| V1.sub-def-identity | closed rec-group + projection equality: structurally equal groups canonicalize equal; group shape, projection or internal-reference differences remain distinct | `calls.wast:13`; `types.wast:23`; `types.wast:25`; `types.wast:27`; `types.wast:29`; `types.wast:31`; `types.wast:33` | 3 | 4 |
| V1.sub-abs | func, extern, exn heap types pairwise unrelated | `types.wast:35`; `types.wast:37`; `types.wast:39`; `types.wast:41`; `types.wast:43`; `types.wast:45`; `types.wast:47` | 1 | 6 |
| V1.rec-group | recursive references inside a group valid; forward reference beyond the group invalid | `types.wast:49`; `types.wast:51`; `types.wast:53`; `types.wast:59` | 3 | 1 |
| V2.bot | unreachable stack: missing operands typed bottom (any type, numbers + refs) | `operands.wast:3`; `operands.wast:5`; `operands.wast:7`; `operands.wast:9` | 2 | 2 |
| V2.refbot-as-non-null | `unreachable ref.as_non_null` result usable as any non-null/nullable ref, never as a number | `operands.wast:11`; `operands.wast:13`; `operands.wast:15`; `operands.wast:17` | 3 | 1 |
| V2.refbot-br-on-null | `unreachable br_on_null l` result = non-null bottom ref | `operands.wast:19`; `operands.wast:21`; `operands.wast:23` | 2 | 1 |
| V2.refbot-br-table | `unreachable ref.as_non_null br_table` over labels `[(ref $a)]`,`[(ref $b)]` valid | `operands.wast:25`; `operands.wast:27`; `operands.wast:93` | 1 | 2 |
| V4.local-get-unset | reading a non-defaultable declared local before any set = invalid | `locals.wast:3`; `locals.wast:5`; `locals.wast:7`; `locals.wast:9` | 2 | 2 |
| V4.local-set-get | set then get in the same sequence = valid; tee also initializes | `locals.wast:11`; `locals.wast:13`; `locals.wast:15`; `locals.wast:17`; `locals.wast:19`; `locals.wast:21`; `locals.wast:59` | 4 | 3 |
| V4.param-set | non-defaultable parameters readable without a set | `locals.wast:23`; `locals.wast:25` | 1 | 1 |
| V4.block-reset | a set inside block/loop/if arm/try_table body does not initialize after the construct | `locals.wast:27`; `locals.wast:29`; `locals.wast:31`; `locals.wast:33`; `locals.wast:35`; `locals.wast:37`; `locals.wast:39`; `locals.wast:41`; `locals.wast:43` | 3 | 6 |
| V4.if-arms | each if arm typed from the entry init state | `locals.wast:45`; `locals.wast:47`; `locals.wast:49`; `locals.wast:51` | 2 | 2 |
| V4.throw | throw x: tag params consumed, stack-polymorphic after; tag index range | `exceptions.wast:3`; `exceptions.wast:5`; `exceptions.wast:7`; `exceptions.wast:9`; `exceptions.wast:11`; `exceptions.wast:13` | 3 | 3 |
| V4.throw-ref | throw_ref: operand (ref null exn) (exnref, (ref exn), bottom); others invalid; polymorphic | `exceptions.wast:15`; `exceptions.wast:17`; `exceptions.wast:19`; `exceptions.wast:21`; `exceptions.wast:23` | 3 | 2 |
| V4.try-table | try_table block typing (params/results, type-index block types) | `exceptions.wast:25`; `exceptions.wast:27`; `exceptions.wast:29`; `exceptions.wast:31` | 2 | 2 |
| V4.catch | catch x l: tag params ≤ label types (subtyping), label index range (labels outside the try_table) | `exceptions.wast:33`; `exceptions.wast:35`; `exceptions.wast:37`; `exceptions.wast:39`; `exceptions.wast:41`; `exceptions.wast:43`; `exceptions.wast:45` | 3 | 4 |
| V4.catch-ref | catch_ref x l: params + (ref exn) ≤ label types | `exceptions.wast:47`; `exceptions.wast:49`; `exceptions.wast:51`; `exceptions.wast:53` | 2 | 2 |
| V4.catch-all | catch_all l: [] ≤ label types | `exceptions.wast:55`; `exceptions.wast:57` | 1 | 1 |
| V4.catch-all-ref | catch_all_ref l: (ref exn) ≤ label types | `exceptions.wast:59`; `exceptions.wast:61`; `exceptions.wast:63`; `exceptions.wast:65` | 2 | 2 |
| V4.return-call | return_call x: callee results ≤ return type (subtyping, arity), params consumed, polymorphic | `calls.wast:15`; `calls.wast:17`; `calls.wast:19`; `calls.wast:21`; `calls.wast:23`; `calls.wast:25` | 3 | 3 |
| V4.return-call-indirect | return_call_indirect: table elem ≤ (ref null func), type index, results ≤ return | `calls.wast:27`; `calls.wast:29`; `calls.wast:31`; `calls.wast:33`; `calls.wast:35` | 2 | 3 |
| V4.return-call-ref | return_call_ref y: operand (ref null $y), results ≤ return | `calls.wast:37`; `calls.wast:39`; `calls.wast:41`; `calls.wast:43`; `calls.wast:45`; `calls.wast:73`; `calls.wast:75` | 3 | 4 |
| V4.call-ref | call_ref y: operand (ref null $y) (non-null accepted), y a function type | `calls.wast:3`; `calls.wast:5`; `calls.wast:7`; `calls.wast:9`; `calls.wast:11`; `calls.wast:13`; `calls.wast:71`; `calls.wast:77` | 4 | 4 |
| V4.ref-as-non-null | ref.as_non_null: (ref null ht) → (ref ht) | `operands.wast:29`; `operands.wast:31`; `operands.wast:33` | 2 | 1 |
| V4.br-on-null | br_on_null l: label types t*, result t* (ref ht) | `operands.wast:35`; `operands.wast:37`; `operands.wast:39` | 1 | 2 |
| V4.br-on-non-null | br_on_non_null l: label last type (ref null? ht) matching operand heap | `operands.wast:41`; `operands.wast:43`; `operands.wast:45`; `operands.wast:47` | 2 | 2 |
| V4.ref-null | ref.null ht: ht valid; result (ref null ht) | `types.wast:69`; `types.wast:71`; `types.wast:73`; `types.wast:75` | 3 | 1 |
| V4.ref-func | ref.func x: result non-null (ref $type-of-x); x must be declared (C.refs) | `calls.wast:57`; `calls.wast:59`; `calls.wast:61` | 1 | 2 |
| V4.ref-is-null | ref.is_null over any reference type | `operands.wast:49`; `operands.wast:51`; `operands.wast:53` | 2 | 1 |
| V4.call-indirect | call_indirect: table elem type ≤ (ref null func) | `calls.wast:47`; `calls.wast:49`; `calls.wast:51`; `calls.wast:53`; `calls.wast:55` | 3 | 2 |
| V4.table-ops | table.get/set/grow/fill/size typed at the table's element type (operand subtyping) | `tables.wast:3`; `tables.wast:5`; `tables.wast:7`; `tables.wast:9`; `tables.wast:11`; `tables.wast:13`; `tables.wast:15`; `tables.wast:17`; `tables.wast:19` | 5 | 4 |
| V4.table-copy-init | table.copy/table.init: source ≤ destination element type | `tables.wast:21`; `tables.wast:23`; `tables.wast:25`; `tables.wast:27`; `tables.wast:29`; `tables.wast:31` | 2 | 4 |
| V4.select | typed select over references; untyped select on references invalid | `operands.wast:55`; `operands.wast:57`; `operands.wast:59`; `operands.wast:61` | 2 | 2 |
| V4.br-table | br_table operands ≤ every label (subtyping), arity | `operands.wast:63`; `operands.wast:65`; `operands.wast:67` | 1 | 2 |
| V4.blocktype-idx | block/loop/if by type index (multi-param/result) | `operands.wast:69`; `operands.wast:71`; `operands.wast:73`; `operands.wast:75` | 3 | 1 |
| V5.types-seq | type section groups validated in order: earlier + own-group references only | `types.wast:49`; `types.wast:51`; `types.wast:55`; `types.wast:57` | 3 | 1 |
| V5.tag | tag type = function type with no results; tag index range | `exceptions.wast:67`; `exceptions.wast:69`; `exceptions.wast:71`; `exceptions.wast:73` | 2 | 2 |
| V5.tag-import-export | tag imports + exports | `exceptions.wast:75`; `exceptions.wast:77`; `exceptions.wast:79` | 1 | 2 |
| V5.imports | import descriptions with typed refs (closed types) | `modules.wast:3`; `modules.wast:5`; `modules.wast:7` | 1 | 2 |
| V5.table-init | table initializer expression: constant, typed at the element type; non-nullable table needs a valid initializer | `tables.wast:33`; `tables.wast:35`; `tables.wast:37`; `tables.wast:39`; `tables.wast:41`; `tables.wast:43`; `tables.wast:45` | 4 | 3 |
| V5.elem-typing | element segment initializers typed at the declared type ((ref func) segments); active mode: segment type ≤ table type | `tables.wast:47`; `tables.wast:49`; `tables.wast:51`; `tables.wast:53`; `tables.wast:55`; `tables.wast:57`; `tables.wast:59`; `tables.wast:61` | 4 | 4 |
| V5.refs | C.refs: ref.func in a function body needs a declaration (elem declare, global/table initializer, export) | `calls.wast:57`; `calls.wast:63`; `calls.wast:65`; `calls.wast:67`; `calls.wast:69` | 4 | 1 |
| V5.global-init | global initializers: constant, typed at the global type (non-null globals) | `modules.wast:9`; `modules.wast:11`; `modules.wast:13`; `modules.wast:15`; `modules.wast:17` | 2 | 3 |
| V5.const-imported | constant global.get of an imported immutable global = valid; of a mutable import = invalid | `modules.wast:19`; `modules.wast:21`; `modules.wast:23`; `modules.wast:25`; `modules.wast:27`; `modules.wast:29`; `tables.wast:45` | 5 | 2 |
| V5.gc-constants | R1 option B: earlier immutable globals in global initializers; all immutable globals in segments; tables see imported globals alone; self/later/mutable reads invalid | `gc-constants.wast:5`; `gc-constants.wast:7`; `gc-constants.wast:9`; `gc-constants.wast:11`; `gc-constants.wast:13`; `gc-constants.wast:15`; `gc-constants.wast:17`; `gc-constants.wast:19`; `gc-constants.wast:21`; `gc-constants.wast:23`; `gc-constants.wast:25`; `gc-constants.wast:27`; `gc-constants.wast:29`; `gc-constants.wast:31`; `gc-constants.wast:33` | 6 | 9 |
| V5.offsets | data/element active offsets: constant i32 | `modules.wast:27`; `modules.wast:29`; `modules.wast:31`; `modules.wast:33`; `modules.wast:35`; `modules.wast:37`; `modules.wast:39` | 2 | 5 |
| V5.start-exports | start function type; export names distinct; export of a tag | `modules.wast:41`; `modules.wast:43`; `modules.wast:45`; `modules.wast:47`; `modules.wast:49`; `modules.wast:51` | 2 | 4 |
| V1.numeric | numeric subtyping = equality | `types.wast:61`; `types.wast:63` | 1 | 1 |
| V1.result | result lists match pointwise with equal arity | `types.wast:65`; `types.wast:67` | 1 | 1 |
| V3.local-runs | mixed runs + neighboring indices + per-function initialization isolation | `locals.wast:53`; `locals.wast:55`; `locals.wast:57` | 1 | 2 |
| V4.call-return | direct call parameters + return results use subtyping | `core-boundaries.wast:3`; `core-boundaries.wast:5`; `core-boundaries.wast:7`; `core-boundaries.wast:9` | 2 | 2 |
| V4.br-if | br + br_if operands use subtyping; br_if restores label types | `core-boundaries.wast:11`; `core-boundaries.wast:13`; `core-boundaries.wast:15`; `core-boundaries.wast:17` | 2 | 2 |
| V4.global-ops | global.get preserves closed type; global.set needs mutability + operand subtype | `core-boundaries.wast:19`; `core-boundaries.wast:21`; `core-boundaries.wast:23`; `core-boundaries.wast:25` | 2 | 2 |
| V4.memarg | memory32 offset boundary; natural alignment; store operand type | `core-boundaries.wast:27`; `core-boundaries.wast:29`; `core-boundaries.wast:31` | 1 | 2 |
| V4.memory | memory32 size/grow operand + result types | `core-boundaries.wast:33`; `core-boundaries.wast:35` | 1 | 1 |
| V4.segment-indices | passive data/elem context; memory.init/table.init/drop index bounds | `core-boundaries.wast:37`; `core-boundaries.wast:39`; `core-boundaries.wast:41` | 1 | 2 |
| V5.limits | memory32 65536-page boundary; table32 u32 bound; min ≤ max | `core-boundaries.wast:43`; `modules.wast:53`; `modules.wast:55`; `modules.wast:57`; `modules.wast:59` | 3 | 2 |
| V5.one-memory | zero/one memory valid; multi-memory negative belongs to profile checks, not this oracle differential (its flags admit multi-memory) | `core-boundaries.wast:45`; `modules.wast:61` | 2 | 0 |
| V5.extended-const | oracle feature flags exclude arithmetic constant expressions | `modules.wast:63` | 0 | 1 |
| V4.label-depth | br/br_if/br_table/br_on_null/catch index = enclosing-label depth invalid; depth − 1 valid; try_table's own label excluded from clauses | `exceptions.wast:43`; `exceptions.wast:81`; `operands.wast:39`; `operands.wast:77`; `operands.wast:79`; `operands.wast:81`; `operands.wast:83`; `operands.wast:85`; `operands.wast:87`; `operands.wast:89`; `operands.wast:91` | 5 | 6 |

## Raw obligations (MAIN)

| rule | case | state + acceptance |
|---|---|---|
| raw.local-max-run | one compressed non-defaultable local run of `2^32 − 1`, no parameters; first/last index; count overflow | raw (MAIN). Binary can encode the count; this suite leaves the impractical oracle expansion unrun. Add direct AST checks for valid unused run, unset last read, index equal to total, and total exceeding the bound. |
| raw.unset-context | direct instruction-typing context with an unset non-defaultable local and no parameters | raw (MAIN) for the context-level API (not source syntax). The module-level read is already expressible and pinned at `locals.wast:5`/`:7`; no claim that this module case needs raw AST. |
| raw.optype-bottom | direct `bot`/`refBot` operands and an attempted source annotation of either | raw (MAIN). Source cannot spell operand bottoms; instruction-produced behavior is pinned by the V2 rows. Add direct matching/annotation checks at the public AST boundary. |
| raw.closed-type-invalid | a closed defined type with an out-of-range projection/recursive reference | raw (MAIN). Binary source carries indices, not FVA's closed-type representation. Add direct well-formedness/closure checks; source-index boundaries are pinned by V1. |

## Evidence

- Oracle = `wasm-tools 1.262.0 (e22db44da)`; flags = `fvatest profile` → `wasmToolsFeatures`. `commands.tsv` records every verdict + negative diagnostic; fixture SHA-256 headers bind these receipts to exact bytes. `scripts/test-p2valid --regen` repeated → byte-identical `commands.tsv` (`cmp`, rc 0).
- Inventory = 290 module commands (137 valid, 153 invalid), 9 WAST files, 63 rule rows (50 seeded + 13 added). Counts in the table count each rule annotation, not distinct modules across rows.
- Profile check = `wasm-tools json-from-wast` for each file → all 290 payloads through `fvatest classify`: 290 `p-prime`, memory count ≤ 1, rc 0. Every positive avoids the manifest's excluded constructs.
- Red first = `FVA_P2VALID_VERBOSE=1 scripts/test-p2valid` against the 2.0 validator at `353c1f103f062bc00d19283398bfe907d3017a7a` → 290 commands; 182 pass (29 valid + 153 invalid); 108 FAIL (valid rejected); 0 pending; rc 1. `base-run.txt` contains the runner hash, command + every case's result.
- `shellcheck scripts/test-p2valid` + `shfmt -d scripts/test-p2valid` (pinned `.tools/bin` tools, project-default tabs) → rc 0. `scripts/test-p2valid --self-test` → 26 pass, 0 FAIL, rc 0; per-control output below.
- Coverage limit = finite rule/boundary examples, not a proof over all modules. This task does not run the full gate, U28c mutation campaign, runtime/link/import matching, or raw-AST checks. E4 plants + proof checking remain MAIN's unit evidence.

## Notes for MAIN

- Seed correction (D1): `Deftype_sub/refl` requires `$clos_deftype(C, deftype_1) = $clos_deftype(C, deftype_2)`. Equal closed rec-group syntax + equal projection canonicalize equal even when declared in separate groups. `types.wast:23`/`:27` accept; group shape `:29`, projection `:25`, internal references `:31` reject. Function signature variance without a declared subtype rejects at `:33`.
- R1 = option B (D2): the separate `gc-constants.wast` group now has 6 valid + 9 invalid, every expected verdict = oracle, 0 pending. SpecTec `Globals_ok/cons` extends the global context after each global; `Module_ok` checks tables under `C′` (imported globals alone), segments under `C`. Thus a table initializer reading a defined global is invalid even with `gc`; `gc-constants.wast:17` records `global index out of bounds`. Earlier immutable global initializers + segment reads accept; own/later/mutable reads reject.
- `call_indirect` need not statically equate its requested type with the table's defined element type: it only requires table elements ≤ `funcref` (`calls.wast:55`, valid). Closed-type equality at actual indirect invocation/import linking belongs to runtime/link suites, not module validation.
- At-most-one-memory is a P′ precondition that the deliberately broad oracle flags do not enforce. This suite pins the positive boundary; the multiple-memory negative belongs to MAIN's profile checks, not an oracle-equal negative here.
- The appendix describes a sketch, not a replacement for the instruction rules. Its `call_ref`/`return_call_ref` pseudocode lists `pop_vals(t.params)` before `pop_val(Ref(Def(types[x])))`; SpecTec 2.3 instead types the input `t_1* (REF NULL (_IDX x))`. The fixtures follow 2.3 + the oracle: args below the reference validate (`calls.wast:3`, `:5`, `:73`); reversed order rejects (`:71`, `:75`); literal null still validates (`:77`). MAIN must resolve the appendix discrepancy against the normative rule, not copy the sketch's pop order.
- V2 example needs an explicit selector: `unreachable ref.as_non_null br_table 0 1` is invalid (`expected i32, found heap type`), as `br_table` first pops an i32 selector. `operands.wast:25` inserts `i32.const 0` and is valid, exercising the intended reference-bottom relation to both distinct label types. `operands.wast:93` pins the missing-selector negative. MAIN must correct the contract's shorthand.
- D3 boundaries: implicit function label contributes one enclosing label; catch clauses exclude the new try_table label (V4.label-depth). Repeated direct set/set/get = `locals.wast:59`; unreachability never initializes locals = `locals.wast:7`; source type indices still require bounds in unreachable code = `types.wast:77`/`:79`.
- Raw run/context checks above remain unconfirmed; this task examines source rules + binary behavior alone. No implementation or proof source was read.

## Harness controls

Command = `scripts/test-p2valid --self-test`, rc 0. The controls use an isolated three-command fixture + stub runner; the real oracle produces its receipt. Runner assertion rc 1 is deliberately ignored when every output row matches. Source receipts require matching command kinds/verdicts, a diagnostic for each invalid module, current feature flags, exact fixture hashes + an exact command inventory.

```text
ok p2valid-driver.regen (rc 0)
ok p2valid-driver.green (rc 0)
ok p2valid-driver.all-valid (rc 1)
ok p2valid-driver.all-invalid (rc 1)
ok p2valid-driver.missing (rc 1)
ok p2valid-driver.duplicate (rc 1)
ok p2valid-driver.extra (rc 1)
ok p2valid-driver.malformed (rc 1)
ok p2valid-driver.misclassified (rc 1)
ok p2valid-driver.setup (rc 2)
ok p2valid-driver.profile-json (rc 2)
ok p2valid-driver.profile-setup (rc 2)
ok p2valid-driver.json-setup (rc 2)
ok p2valid-driver.crash (rc 3)
ok p2valid-driver.profile-crash (rc 3)
ok p2valid-driver.json-crash (rc 3)
ok p2valid-driver.oracle-setup (rc 2)
ok p2valid-driver.oracle-crash (rc 3)
ok p2valid-driver.duplicate-manifest (rc 2)
ok p2valid-driver.missing-manifest-row (rc 2)
ok p2valid-driver.expected-not-oracle (rc 2)
ok p2valid-driver.kind-not-oracle (rc 2)
ok p2valid-driver.missing-oracle-diagnostic (rc 2)
ok p2valid-driver.changed-fixture-bytes (rc 2)
ok p2valid-driver.missing-manifest (rc 2)
ok p2valid-driver.empty-fixtures (rc 2)
test-p2valid driver: 26 pass; 0 FAIL
```
