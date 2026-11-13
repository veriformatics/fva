# P′ execution suite coverage (U28b E3; tester-3)

Source: `docs/contracts/U28b-runtime.md` (C2 S1–S5, C1 R1–R5) + Wasm 3.0 SpecTec `859d3232`.
42 obligations = 41 seeded + R5 store extension. `scripts` = observing commands;
`wasmtime` = script verdict; `c1` = actual outcome classes + counts from `c1-outcomes.tsv`.
`pass` at C1 is a control, not E4 mutation credit. `commands.tsv` pins C2 expectations;
C2 execution is MAIN's next check. `notes` = discriminating values + observable-domain limits.

| id | obligation | scripts | wasmtime | c1 | notes |
|---|---|---|---|---|---|
| S1.outside-label | `try_table` handler sits outside its result label: `br 0` from the body exits the try_table, no catch runs | contexts.wast:52 | pass | fail (1) | `br 0` leaves the try_table result label; normal continuation returns 17, catch path 99. |
| S1.br-skips-handler | a `br` to an outer block crosses a handler without counting it (label indices ignore handlers) | contexts.wast:53 | pass | fail (1) | Outer-label branch returns 31; counting the handler changes its target and exposes 97/stuck. |
| S1.return-crosses | `return` from inside a try_table body leaves the function; the handler is dropped | contexts.wast:54 | pass | fail (1) | Return inside handler returns 43; post-handler fallthrough returns 99. |
| S1.tail-drops-handler | a tail call from inside a try_table drops the handler: the callee's throw is not caught by it | tail.wast:101,102,103,104,105 | pass | fail (5) | Direct/ref/indirect tail callees throw uncaught; ordinary-call and caller-of-tailer controls catch payload 181. |
| S1.trap-passes | a trap passes every handler, `catch_all`/`catch_all_ref` included | contexts.wast:55,56 | pass | fail (2) | Nested catch_all and catch_all_ref do not intercept unreachable; both invocations trap. |
| S1.handler-vals | a body that completes normally leaves its values; block type with params (values enter the body) | contexts.wast:57,58 | pass | fail (2) | Typed try_table consumes i32/i64 params and completes with transformed pairs (14,24) and (0,0). Raw handlerExit without an arity premise needs a direct malformed-config fixture. |
| S2.throw-payload | `throw x` payload in operand order (multi-value, mixed types) delivered by `catch` | exceptions.wast:200; payload-refs.wast:56,57,58,59 | pass | fail (5) | Mixed i32/i64/f32/f64 preserves -17, large i64, signed zero and 1.5; reference fields select two distinct functions; boxed exnref and zero-arity tags exercise reference/empty payload boundaries. |
| S2.throw-ref-null | `throw_ref` on a null exnref traps | exceptions.wast:214 | pass | fail (1) | A source null exnref followed by throw_ref traps, rather than returning or throwing. |
| S2.propagate-label | a throw inside nested blocks/loops/ifs (residual operands below) reaches the enclosing handler | exceptions.wast:205,206 | pass | fail (2) | Both if branches throw through loop/block/try labels with i32/i64 residual operands; expected pairs (17,29)/(31,47) exclude leaked operands. |
| S2.propagate-frame | a throw in a callee (several frames deep) reaches the caller's handler | exceptions.wast:207; properties.wast:33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64 | pass | fail (33) | Three call frames + residual operands produce (53,71); fixed-seed round trips add 32 boundary/generated payloads through two frames. |
| S2.no-match | a handler without a matching clause propagates to the next enclosing handler | exceptions.wast:208 | pass | fail (1) | A nonmatching same-typed tag and an empty inner handler both propagate to outer catch; payload remains (79,83). |
| S2.catch | `catch x l`: payload values, then `br l` | exceptions.wast:200,201,202; payload-refs.wast:59 | pass | fail (4) | Tagged catch returns exact fields, including MIN/MAX/zero/-1 and empty payload; branch delivery is observed as returned values. |
| S2.catch-ref | `catch_ref x l`: payload values + the exnref, then `br l` | exceptions.wast:203,204; payload-refs.wast:56,57; properties.wast:33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64 | pass | fail (36) | Fields precede the exnref: locals consume ref,y,x, then rethrow returns (x,y,x,y). Mixed typed-function/i64 payload calls the delivered function; 32 generated round trips preserve every sampled pair. |
| S2.catch-all | `catch_all l`: no values, `br l` | exceptions.wast:209 | pass | fail (1) | Two payload values are discarded and the branch returns 19; the fallthrough control is 99. |
| S2.catch-all-ref | `catch_all_ref l`: the exnref alone, `br l` | exceptions.wast:210 | pass | fail (1) | The sole delivered exnref rethrows the original (89,97) payload to an outer tagged catch. |
| S2.clause-order | the first matching clause wins (tagged before catch_all and after; a non-matching tagged clause skipped) | exceptions.wast:211,212 | pass | fail (2) | A nonmatching first clause is skipped; tagged-before-all returns -1, all-before-tag returns 23 instead of 99. |
| S2.tag-identity | tags match by address: two tags of one type are distinct; an imported alias of a tag matches it | exceptions.wast:213; tags.wast:49,50,78 | pass | fail (4) | Same-typed distinct tags return (101,103), not wrong-catch (-1,-2); imported shared/alias tag addresses both catch exact payloads. |
| S2.handler-frame | the handler's own module resolves its tag index (thrower and catcher in different modules with different tag index maps) | tags.wast:49,51,77 | pass | fail (3) | Origin resolves shared tag at index 1; catcher resolves it at index 0 with noise at 1. Results 239/251/271 exclude the wrong-map +1000/+2000 paths. |
| S2.rethrow | `catch_ref` → `throw_ref` rethrows the same exception: its payload reaches an outer `catch` unchanged | exceptions.wast:203,204,210,219,220,221,222,228,229; payload-refs.wast:58; properties.wast:33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64 | pass | fail (42) | catch_ref/catch_all_ref and boxed exnref preserve payloads. A saved reference survives intervening exceptions and a new module/tag; store witnesses remain global 127, memory 131. Exact address/store equality requires the direct normalization fixture, not category-only assert_exception. |
| S2.cross-module | a tag exported by one module and imported by another: throw in one, catch in the other | tags.wast:49,50,75 | pass | fail (3) | Registered origin exports tags/functions; catcher imports reordered tags and catches origin throws; later module imports catcher-owned tag/function. |
| S3.return-call | `return_call x` (results, params, deep tail recursion beyond any frame budget) | tail.wast:90,91,92,93,106 | pass | fail (4); pass (1) | Mixed result/parameter order, residual operands, host callee and 12000 tail-recursive calls return exact values; zero-depth control returns 17. |
| S3.return-call-ref | `return_call_ref y` on a function reference; on null it traps | tail.wast:94,95,107 | pass | fail (3) | Typed reference returns (34,18), null traps, and imported print_i32 host callee returns no values. |
| S3.return-call-indirect | `return_call_indirect`: success, type mismatch trap, null entry trap, out-of-bounds trap | tail.wast:96,97,98,99,100,108 | pass | fail (6) | Correct entry returns (36,22); wrong type, null entry, table-size index and unsigned-MAX index trap; host entry returns no values. |
| S3.drops-labels | a tail call from inside nested blocks returns the callee's results to the caller's caller | tail.wast:90,91 | pass | fail (2) | A tail call inside two blocks discards residual i32/i64 operands and both labels; returns (30,16)/(0,0), not wrapper continuation. |
| S4.call-ref | `call_ref y`: call through a reference; null traps | references.wast:69,70 | pass | fail (2) | Non-null reference calls the selected function and returns 230; otherwise-identical null invocation traps. |
| S4.as-non-null | `ref.as_non_null`: null traps, else the value | references.wast:71,72 | pass | fail (2) | Non-null value remains callable and returns 234; null traps before the call. |
| S4.br-on-null | `br_on_null l`: null branches (no value), else the value stays | references.wast:73,74 | pass | fail (2) | Null branches with its prefix only (212); non-null keeps the reference for call_ref (219). |
| S4.br-on-non-null | `br_on_non_null l`: null falls through (dropped), else branches with the value | references.wast:75,76 | pass | fail (2) | Null drops the reference and falls through to g (224); non-null branches carrying f (218). |
| S5.uncaught | an uncaught exception ends the invocation (`assert_exception`), distinct from a trap and a return | exceptions.wast:215,217,218; payload-refs.wast:60 | pass | fail (2); pass (2) | assert_exception is paired with ordinary return 113 and unreachable trap controls; empty-payload uncaught throw is included. |
| S5.uncaught-deep | an exception escaping several frames and handlers without a match | exceptions.wast:216 | pass | fail (1) | The exception escapes several frames, an empty handler and a nonmatching handler; assert_exception distinguishes it from trap/return. Direct fixture must pin Outcome.thrown address/store and SysFinal abnormal. |
| R1.rec-identity | iso-recursive identity: identical rec groups are one type (indirect call / import succeeds); identical expanded signatures in differently shaped groups are distinct (trap / unlinkable) | types.wast:69,70,71,72,73,74,75,76 | pass | pass (8) | Equal two-member groups at different offsets link indirectly; projections 0/1, singleton-vs-two-member and recursively self-referential singleton-vs-wide groups remain distinct despite matching expanded signatures. |
| R1.nonzero-offset | types defined at nonzero group offsets and referring to earlier types close correctly (indirect call by such a type) | types.wast:77,78 | pass | pass (2) | Two acceptor types close over equal earlier i64-function types at different nonzero offsets; indirect calls return 282 for null, 281 for ref.func. |
| R1.import-deftype | function import matching by defined type: same canonical type links, a different group shape is unlinkable | types.wast:95,107,110,115,122,127 | pass | pass (6) | Canonical equal function/tag groups link after an extra preceding type; singleton-vs-two-member and projection mismatch are unlinkable for both functions and tags. |
| R2.null | source `ref.null ht` vs the runtime null: `ref.is_null`, nulls of different heap types returned and passed | initializers.wast:36; references.wast:79,80,81,82,83,84,85,86,87 | pass | pass (10) | Source nulls of func/extern/exn/defined types execute and pass internally/through actions; generic/same-heap expectations match. All null tests return 1; ref.func control returns 0. Wasmtime rejects cross-heap typed expectations, so MAIN owns that direct runner fixture. |
| R2.nondefaultable-local | a local of non-null reference type set before it is read | references.wast:77,78 | pass | fail (1); pass (1) | A non-null typed local is set before get: ref.is_null returns 0 and call_ref returns 242. Reading an unset local is invalid source, so direct fixture must reject local.get none rather than invent null. |
| R2.table-init | a table with an explicit non-null initializer (`ref.func`): elements hold that reference | initializers.wast:30,31,32,33,34,35,36,57 | pass | pass (8) | All elements of explicit non-null table call f (+23), including first/last; boundary index traps; zero-length and default-null table controls pin sizes/nullness; nullable import of non-null table is unlinkable. |
| R2.global-init | a non-null reference global initialized by `ref.func` | initializers.wast:37,38 | pass | fail (1); pass (1) | Non-null global reads as non-null and calls distinct g (+29), excluding an invented default or wrong function reference. |
| R3.block-type | a block/loop/if typed by a function type index with params | types.wast:79,80,81 | pass | pass (3) | Block/loop/if expand a two-parameter/two-result type index on both if paths; a parametric loop branches three times and returns (0,338). |
| R3.call-indirect-type | `call_indirect` compares defined types (subtype-free P′: equality) | types.wast:69,70,71,72,73,74 | pass | pass (6) | Canonical equal defined types succeed; same expanded signatures from different group projections/shapes trap. |
| R4.tag-alloc | instantiation allocates a module's own tags after imported ones; exported tags expose their addresses | tags.wast:52,75,76,77 | pass | fail (4) | Origin, catcher-owned and later fresh same-typed tags remain distinct; imported tags retain aliases/identity after further module/tag allocations. |
| R4.global-import-sub | an immutable global import of a subtype links (`(ref func)` exported, `(ref null func)` imported); a mutable one must match exactly (else unlinkable) | initializers.wast:40,46,49,53 | pass | pass (4) | Immutable (ref func) links to nullable func; exact mutable type links. Mutable-nullability widening and immutable nullable-to-non-null imports are unlinkable. |
| R5.store-extension | later exception/tag allocations preserve an earlier exception, its tag and its fields | exceptions.wast:219,220,221,222,228,229 | pass | fail (6) | Save payload (149,151) as exnref, allocate unrelated exceptions, instantiate a new module/tag, then rethrow the old ref: same payload/tag. Global/memory writes survive unwinding. Exact whole-store extension and malformed lookups need direct Lean fixtures. |

## Run evidence

- Oracle = wasmtime 50.0.0; encoder = wasm-tools 1.262.0. Flags come from `fvatest profile`:
  `-W exceptions=y,tail-call=y,function-references=y,gc=y`.
- C1 invocation + binary SHA256 + full output = `c1-run.txt`; exact per-command trace =
  `c1-outcomes.tsv` (165 identities, same order as `commands.tsv`; 62 pass / 103 fail / 0 skip).
  C1 build's source revision was not supplied; its full binary hash is pinned in the capture.
- Command: `FVA_P2_BIN=<C1 binary> scripts/test-p2exec` → rc 1 (expected red).
  Every script's independent `wasmtime wast` run passes; no out-of-profile or typing skips.
- `FVATest/P2/check-driver` → rc 0, 20 pass / 0 fail. Cases pin successful matching, failure,
  missing/duplicate/extra/malformed commands, wrong identity/class/skip reason, oracle failure,
  setup and crash exit codes. A copy of the checker forced to `exit 0` → fixture rc 1,
  1 pass / 19 fail (planted check fires).
- `shellcheck scripts/test-p2exec FVATest/P2/{check-driver,make-commands,make-properties}`
  and `shfmt -d` over the same files → rc 0.
- `FVATest/P2/make-properties | cmp - FVATest/P2/properties.wast` → rc 0;
  `FVATest/P2/make-commands | cmp - FVATest/P2/commands.tsv` → rc 0.
  Regenerate with those scripts, then replace the generated file only when the source changes.
- Placeholder validator prints 0 (grep rc 1); positive control `R5.store-extension` prints 1.

| script | commands | wasmtime | C1 pass | C1 fail | C1 skip |
|---|---:|---|---:|---:|---:|
| contexts.wast | 8 | pass | 1 | 7 | 0 |
| exceptions.wast | 27 | pass | 4 | 23 | 0 |
| initializers.wast | 16 | pass | 15 | 1 | 0 |
| payload-refs.wast | 6 | pass | 1 | 5 | 0 |
| properties.wast | 33 | pass | 1 | 32 | 0 |
| references.wast | 20 | pass | 11 | 9 | 0 |
| tags.wast | 13 | pass | 5 | 8 | 0 |
| tail.wast | 20 | pass | 2 | 18 | 0 |
| types.wast | 22 | pass | 22 | 0 | 0 |
| total | 165 | pass | 62 | 103 | 0 |

## Direct-fixture boundaries

Valid scripts cannot construct malformed runtime states. The following checks remain MAIN's
Lean/runner-fixture work; this suite claims their observable slices alone.

| fixture | why scripts cannot decide it | direct check |
|---|---|---|
| Closed-type domains | Valid type indices/projections only | Invalid projection expands to none; roll/close/expand identities on their stated well-formedness domains |
| Unset local | The validator rejects reading it | `local.get` on `none` has no reduction; it never invents null |
| Raw handler exit | Valid execution obeys result arity | `handlerExit` accepts any values without an extra arity premise |
| Missing lookups | Well-formed store/module maps supply addresses | Import matching fails on absent lookup; missing/different catch tag or exception lookup takes handler-next |
| Throw normalization | `assert_exception` exposes only the category | Every administrative propagation preserves exact store/address; caught `runDet` continues; uncaught is final; `SysFinal` is abnormal with exit priority kept |
| Store extension | Script hosts cannot propose arbitrary stores | Appending preserves old tag identities and old exception tag/fields; a deleting/changing extension fails |
| Cross-heap typed null patterns | Wasmtime distinguishes typed null expectations; SpecTec runner.ml:476 matches all null patterns | Direct runner fixture: func-null matches an extern-null expectation and conversely (MAIN's accepted N1 ruling) |

The 32 property cases use eight boundary pairs + 24 fixed-seed pairs (seed `0x50325032`):
catch_ref → unrelated exception allocation → throw_ref must preserve the original i32/i64 pair.
This is sampled compiled behavior, not a universal proof. The 12000-call tail case is finite
stress; handler-lifetime and result/parameter probes supply the semantic controls.

C2 execution, E4 production-rule plants, direct Lean fixtures and the full FVA gate were not
run by this blind author. No implementation/spec Lean source was read or changed.

tester-3-DONE-1
