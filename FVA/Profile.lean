/-!
# FVA's Wasm profile P′ (support manifest, contract U28a E7)

One source for what FVA decodes: the normative pins, the constructs inside P′, the classes of
constructs outside it (the decoder's `unsupported` verdicts and the test classifier name the
same classes), and the oracle flags that select in-profile official test modules. Test scripts
read it through `fvatest profile`; the README's profile table is generated from it.
-/

namespace FVA.Profile

/-- Manifest version; any change to the lists below bumps it. -/
def version : Nat := 1

/-- Normative pins: the Wasm 3.0 specification (SpecTec) and the official testsuite. -/
def specPin : String := "WebAssembly/spec@859d3232a55cdbb9d75343a072b05cd0a2172e1a"
/-- The official testsuite revision every pinned script comes from. -/
def testsuitePin : String := "WebAssembly/testsuite@44f1503f98409fa3737437bf9449a37a5def4210"

/-- Constructs inside P′, as the README lists them. -/
def included : List String :=
  [ "Wasm 2.0 without SIMD: numeric, reference, parametric, variable, table, memory and " ++
      "control instructions; bulk memory; multi-value; one memory",
    "exception handling: tags, throw, throw_ref, try_table with catch, catch_ref, catch_all, " ++
      "catch_all_ref; exnref",
    "tail calls: return_call, return_call_indirect, return_call_ref",
    "function references: call_ref, ref.as_non_null, br_on_null, br_on_non_null, non-null " ++
      "and typed references, table initializers",
    "recursive type groups (rec) of final function types without declared supertypes" ]

/-- Construct classes outside P′. The decoder reports the first one it meets as `unsupported`;
the tests' profile classifier lists every one a module's text shows. -/
inductive Excluded where
  /-- Struct and array types, sub types that are not final or declare a supertype; the any, eq,
  i31, struct, array and none heap types. -/
  | gcTypes
  /-- The bottom heap types nofunc, noextern and noexn (a scope choice: no pinned P′ script
  uses them). -/
  | bottomTypes
  /-- `0xFB`-prefixed instructions and `ref.eq`. -/
  | gcInstrs
  /-- `v128` and `0xFD`-prefixed instructions. -/
  | simd
  /-- Shared memories and tables, `0xFE`-prefixed instructions. -/
  | threads
  /-- 64-bit memory and table addresses. -/
  | memory64
  /-- An instruction's memory index other than 0 (a second memory: validation's). -/
  | multiMemory
  /-- Legacy exception handling: try, catch, catch_all, delegate, rethrow. -/
  | legacyEh
  deriving DecidableEq, Repr

/-- Every excluded class. -/
def Excluded.all : List Excluded :=
  [.gcTypes, .bottomTypes, .gcInstrs, .simd, .threads, .memory64, .multiMemory, .legacyEh]

/-- The class's stable identifier (decoder messages, classifier output, manifest JSON). -/
def Excluded.id : Excluded → String
  | .gcTypes => "gc-types" | .bottomTypes => "bottom-types" | .gcInstrs => "gc-instructions"
  | .simd => "simd"
  | .threads => "threads" | .memory64 => "memory64" | .multiMemory => "multi-memory"
  | .legacyEh => "legacy-exceptions"

/-- `wasm-tools validate` features admitting P′: `gc` for function-only `rec` groups and typed
references, `multi-memory` + `memory64` for 3.0's spellings of P′ (padded memory indices, `u64`
limits); the profile classifier excludes the GC, bottom, multi-memory and memory64 constructs
these admit, and `extended-const` stays off. -/
def wasmToolsFeatures : String :=
  "wasm2,-simd,exceptions,tail-call,function-references,gc,multi-memory,memory64"
/-- `wasmtime wast` flags running P′ scripts. -/
def wasmtimeFlags : String := "-W exceptions=y,tail-call=y,function-references=y,gc=y"

end FVA.Profile
