import FVATest.Subjects.EdgerCpm.Contract

/-!
# edgeR raw CPM: library-size-vector form (U14 S4; reviewed)

This claim concerns `calc_cpm_raw` in the shipped `edgeR.so`. The caller supplies an `n`-gene by
`m`-sample count matrix, stored column-major in `cpm`, and one library size per sample. The call
replaces each count by its product with 1,000,000, divided by the library size. Both operations
use binary64 rounding; NaN results follow WebAssembly's permitted result sets.

The claim covers positive dimensions, at most 1 GiB of count and library-size bytes, and every
input bit pattern. The library descriptor has type 2 and no row selection. The call assumes the
stated memory layout, linked code, successful loader preparation and allocator contract
(`FVATest/Subjects/EdgerCpm/Contract.lean`). It does not verify R's allocator, the R wrapper or
the rest of edgeR.
-/

namespace Subjects.EdgerCpm

open FVA.Wasm FVA.Wasm.Exec

/-- Every covered input has an admissible call. Every admissible call terminates without a trap,
returns no values, leaves each cell with an allowed CPM result, and preserves the kept input
bytes. The `nthreads` argument is arbitrary; this binary does not use it. -/
def claim : Prop :=
  (∀ x, Domain x → ∃ H l s inst, Admissible H x l s inst) ∧
  ∀ x H l s inst, Domain x → Admissible H x l s inst → ∀ nth : BitVec 32,
    CallReturns H s inst "calc_cpm_raw"
      [.i32 (.ofNat 32 l.y), .i32 (.ofNat 32 l.lib), .i32 (.ofNat 32 l.c), .i32 nth]
      fun s' vs => vs = [] ∧
        (∀ i < x.n, ∀ j < x.m, ∃ out, Holds s' (l.cell x i j) (le64 out) ∧
          CpmElem (x.count i j) (x.libSize j) out) ∧
        SameOn s s' (l.kept x)

end Subjects.EdgerCpm
