import FVATest.Subjects.EdgerCpm.Lifted
import FVA.Spec.CAbi
import FVA.Spec.Exec.Host
import FVA.Spec.Exec.Instantiate

/-!
# edgeR raw CPM: the contract vocabulary (U14 S4; reviewed with `Spec`)

The definitions `Spec.claim` is stated with: the cell result, the input and its layout, the
allocator contract, the code binding and the admissible call. They sit apart from the spec module
because a structure declares theorems (constructor injectivity, a `Prop` structure's fields) that
`fva trust` would read as claims.
-/

namespace Subjects.EdgerCpm

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- The little-endian bytes of a 64-bit value (a C `double` in memory). -/
def le64 (x : BitVec 64) : List UInt8 := Binary.leBytes 8 x.toNat

/-- One cell's result: multiply the count by 1,000,000, then divide by the library size.
Each operation follows WebAssembly's binary64 result set, including its NaN choices. -/
def CpmElem (count lib out : BitVec 64) : Prop :=
  ∃ t ∈ fmul f64fmt (ofBits f64fmt count) (ofBits f64fmt 0x412E848000000000),
    ofBits f64fmt out ∈ fdiv f64fmt t (ofBits f64fmt lib)

/-- The call's input: `n` genes × `m` samples, the counts (gene, sample) and the library sizes
(sample). -/
structure Input where
  /-- Genes (matrix rows). -/
  n : Nat
  /-- Samples (matrix columns). -/
  m : Nat
  /-- The count of gene `i` in sample `j`. -/
  count : Nat → Nat → BitVec 64
  /-- The library size of sample `j`. -/
  libSize : Nat → BitVec 64

/-- Positive gene and sample counts; count and library-size bytes total at most 1 GiB. -/
def Domain (x : Input) : Prop := 0 < x.n ∧ 0 < x.m ∧ 8 * x.n * x.m + 8 * x.m ≤ 2 ^ 30

/-- Where the caller put the call's data in memory 0: the count matrix's descriptor `y` (edgeR's
`cmx`: `nrow` at offset 8, `ncol` at 12), the library sizes' descriptor `lib` (data pointer at 0,
`ncol` at 12, compression type at 16, row selection at 28), the library sizes `d` and the counts
`c`. -/
structure Layout where
  /-- The count matrix's descriptor. -/
  y : Nat
  /-- The library sizes' descriptor. -/
  lib : Nat
  /-- The library sizes, one `double` per sample. -/
  d : Nat
  /-- The counts, one `double` per cell, column-major; the results replace them. -/
  c : Nat

/-- The address of gene `i`'s count in sample `j`. -/
def Layout.cell (l : Layout) (x : Input) (i j : Nat) : Nat := l.c + 8 * (i + x.n * j)

/-- Bytes preserved by the call: the dimensions in `y`, the complete library-size descriptor,
and the library-size vector. -/
def Layout.kept (l : Layout) (x : Input) (a : Nat) : Prop :=
  (l.y + 8 ≤ a ∧ a < l.y + 16) ∨ (l.lib ≤ a ∧ a < l.lib + 32) ∨ (l.d ≤ a ∧ a < l.d + 8 * x.m)

/-- The addresses of the counts. -/
def Layout.counts (l : Layout) (x : Input) (a : Nat) : Prop := l.c ≤ a ∧ a < l.c + 8 * x.n * x.m

/-- Memory 0 holds the call's data: the dimensions, the library sizes' descriptor (data pointer
`d`, `m` columns, type 2, no row selection), the library sizes and the counts. -/
def Data (s : Store) (x : Input) (l : Layout) : Prop :=
  Holds s (l.y + 8) (le32 (.ofNat 32 x.n) ++ le32 (.ofNat 32 x.m)) ∧
  Holds s l.lib (le32 (.ofNat 32 l.d)) ∧
  Holds s (l.lib + 12) (le32 (.ofNat 32 x.m) ++ le32 2) ∧ Holds s (l.lib + 28) (le32 0) ∧
  (∀ j < x.m, Holds s (l.d + 8 * j) (le64 (x.libSize j))) ∧
  ∀ i < x.n, ∀ j < x.m, Holds s (l.cell x i j) (le64 (x.count i j))

/-- Memory 0 exists in `s` and `s'`, is no smaller in `s'`, and keeps every byte at an address in
`keep`. -/
def SameOn (s s' : Store) (keep : Nat → Prop) : Prop :=
  ∃ mem mem', s.mems[0]? = some mem ∧ s'.mems[0]? = some mem' ∧ mem.size ≤ mem'.size ∧
    ∀ a, keep a → a < mem.size → mem'.byte a = mem.byte a

/-- Address `a` lies in one of the blocks (start, size) `bs`. -/
def InBlocks (bs : List (Nat × Nat)) (a : Nat) : Prop := ∃ b ∈ bs, b.1 ≤ a ∧ a < b.1 + b.2

/-- Contract for the imported allocator (`alloc` = `R_chk_calloc(n, size)`, `free` =
`R_chk_free(p)`), which owns the addresses in `heap`; `blocks s` lists the blocks (start, size)
live in `s`. `ready k s` guarantees `k` further positive allocations of at most `cap` bytes. Each
allocation returns fresh zero bytes below 2³² and consumes one guarantee. Allocation and free
preserve caller bytes outside `heap` and other tracked live blocks. Free may change the freed
block and private heap metadata. Guest writes outside the allocator's free bytes preserve both
the live-block abstraction and readiness. This is an assumption on the imports, not a proof of
R's allocator or a guarantee under memory exhaustion. -/
structure Allocator (H : HostSem) (alloc free : Nat) (heap : Nat → Prop) (cap : Nat)
    (blocks : Store → List (Nat × Nat)) (ready : Nat → Store → Prop) : Prop where
  /-- A ready positive allocation returns a fresh zeroed block. -/
  alloc : ∀ k s (n sz : BitVec 32), ready (k + 1) s →
    0 < n.toNat * sz.toNat → n.toNat * sz.toNat ≤ cap →
    (∃ o, H alloc s [.i32 n, .i32 sz] o) ∧
    ∀ o, H alloc s [.i32 n, .i32 sz] o → ∃ s' p, o = .returned s' [.i32 p] ∧
      Store.Extends s s' ∧ ready k s' ∧ p.toNat + n.toNat * sz.toNat ≤ 2 ^ 32 ∧
      (∀ a, p.toNat ≤ a → a < p.toNat + n.toNat * sz.toNat → heap a ∧ ¬ InBlocks (blocks s) a) ∧
      Holds s' p.toNat (List.replicate (n.toNat * sz.toNat) 0) ∧
      (p.toNat, n.toNat * sz.toNat) ∈ blocks s' ∧ (∀ b ∈ blocks s, b ∈ blocks s') ∧
      SameOn s s' fun a => ¬ heap a ∨ InBlocks (blocks s) a
  /-- Freeing a live block keeps the rest. -/
  free : ∀ k s (p : BitVec 32) (z : Nat), ready k s → (p.toNat, z) ∈ blocks s →
    (∃ o, H free s [.i32 p] o) ∧
    ∀ o, H free s [.i32 p] o → ∃ s', o = .returned s' [] ∧ Store.Extends s s' ∧
      ready k s' ∧ (∀ b ∈ blocks s, b.1 ≠ p.toNat → b ∈ blocks s') ∧
      SameOn s s' fun a => ¬ heap a ∨ InBlocks ((blocks s).filter (·.1 ≠ p.toNat)) a
  /-- Guest writes outside the allocator's free bytes keep the live blocks and readiness. -/
  frame : ∀ k s mem mem', ready k s → s.mems[0]? = some mem →
    mem'.pages = mem.pages → mem'.max = mem.max →
    (∀ a, heap a → ¬ InBlocks (blocks s) a → mem'.byte a = mem.byte a) →
      blocks { s with mems := s.mems.set 0 mem' } = blocks s ∧
      ready k { s with mems := s.mems.set 0 mem' }

/-- `inst` in `s` runs this module's code: the exported raw-CPM function and `get_row` (function
207) are the decoded functions, closed over `inst`; functions 12 and 13 (imports `R_chk_calloc`,
`R_chk_free`) are the host functions `alloc` and `free`; the instance's memory 0 is the store's
memory 0. -/
def Linked (s : Store) (inst : ModuleInst) (alloc free : Nat) : Prop :=
  inst.mems[0]? = some 0 ∧
  ∃ a160 a207 a12 a13, inst.funcs[207]? = some a207 ∧
    inst.funcs[12]? = some a12 ∧ inst.funcs[13]? = some a13 ∧
    inst.exportFunc "calc_cpm_raw" = some a160 ∧
    s.funcs[a160]? = some (.wasm (Lifted.module.types.getD Lifted.func86.type ⟨[], []⟩) inst
      Lifted.func86) ∧
    s.funcs[a207]? = some (.wasm (Lifted.module.types.getD Lifted.func133.type ⟨[], []⟩) inst
      Lifted.func133) ∧
    s.funcs[a12]? = some (.host ⟨[.num .i32, .num .i32], [.num .i32]⟩ alloc) ∧
    s.funcs[a13]? = some (.host ⟨[.num .i32], []⟩ free)

/-- A loader-prepared call with the linked code, caller data, two guaranteed scratch allocations,
protected input/output bytes and non-wrapping addresses. Caller buffers may be live heap
blocks. -/
def Admissible (H : HostSem) (x : Input) (l : Layout) (s : Store) (inst : ModuleInst) : Prop :=
  (∃ env imports loaded ps,
    LoaderReady H Lifted.module env imports loaded inst ∧ loaded.prep ps = some s) ∧
  Data s x l ∧
  (∃ alloc free heap blocks ready, Linked s inst alloc free ∧
    Allocator H alloc free heap (8 * x.m) blocks ready ∧ ready 2 s ∧
    ∀ a, l.kept x a ∨ l.counts x a → ¬ heap a ∨ InBlocks (blocks s) a) ∧
  (∀ a, l.kept x a → ¬ l.counts x a) ∧
  l.y + 16 ≤ 2 ^ 32 ∧ l.lib + 32 ≤ 2 ^ 32 ∧ l.d + 8 * x.m ≤ 2 ^ 32 ∧
  l.c + 8 * x.n * x.m ≤ 2 ^ 32

end Subjects.EdgerCpm
