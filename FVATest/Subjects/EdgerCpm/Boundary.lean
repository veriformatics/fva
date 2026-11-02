import FVATest.Subjects.EdgerCpm.Proof
import FVA.Proof.Numerics.Adequacy
import FVA.Proof.Numerics.Arith
import FVA.Proof.Numerics.Convert
import FVA.Proof.Lib.Instance

/-!
# filterByExpr's exact-threshold boundary on the shipped binary (T4 R2, D40)

A sample of median library size 18 with exactly `min.count` = 10 reads: R's cutoff is
`10 / 18 * 1e6` (two binary64 roundings, `0x4120F4471C71C71D` = 555555.55555555562), the binary's
CPM is `10 * 1e6 / 18` (`0x4120F4471C71C71C` = 555555.5555555555), one ulp below, so `cpm ≥ cutoff`
drops the gene. Both values follow from the float spec; the binary's from `claim_holds`.
-/

namespace Subjects.EdgerCpm

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num FVal

/-- The only non-NaN member of a deterministic operator's result set, from the verified
implementation's member. -/
private theorem det_eq {S : Set FVal} (hd : Det S) {v w : FVal} (hv : v ∈ S) (hw : w ∈ S)
    (hn : ¬ v.IsNaN) : w = v :=
  (hd v hv w hw hn).symm

private theorem notNaN {b : BitVec 64} (h : Impl.isNaN (ofBits f64fmt b) = false) :
    ¬ (ofBits f64fmt b).IsNaN := by
  rw [← isNaN_iff, h]; decide

private theorem ofBits_inj {a b : BitVec 64} (h : ofBits f64fmt a = ofBits f64fmt b) : a = b := by
  rw [← fbits_ofBits f64fmt_sane a, ← fbits_ofBits f64fmt_sane b, h]

/-- The binary's CPM element for count 10 and library size 18: 555555.5555555555. -/
theorem cpmElem_10_18 {out : BitVec 64}
    (h : CpmElem 0x4024000000000000 0x4032000000000000 out) : out = 0x4120F4471C71C71C := by
  obtain ⟨t, ht, ho⟩ := h
  have wf := ofBits_wf f64fmt_sane
  have hm := fmul_mem f64fmt_sane (wf 0x4024000000000000) (wf 0x412E848000000000)
  have e1 : Impl.fmul f64fmt (ofBits f64fmt 0x4024000000000000)
      (ofBits f64fmt 0x412E848000000000) = ofBits f64fmt 0x416312D000000000 := by decide +kernel
  rw [e1] at hm
  have ht' := det_eq (fmul_det f64fmt_sane _ _) hm ht (notNaN (by decide +kernel))
  subst ht'
  have hd := fdiv_mem f64fmt_sane (wf 0x416312D000000000) (wf 0x4032000000000000)
  have e2 : Impl.fdiv f64fmt (ofBits f64fmt 0x416312D000000000)
      (ofBits f64fmt 0x4032000000000000) = ofBits f64fmt 0x4120F4471C71C71C := by decide +kernel
  rw [e2] at hd
  exact ofBits_inj (det_eq (fdiv_det f64fmt_sane _ _) hd ho (notNaN (by decide +kernel)))

/-- R's cutoff `min.count / median(lib.size) * 1e6` for 10 and 18: 555555.55555555562. -/
theorem rCutoff_10_18 {q c : FVal}
    (hq : q ∈ fdiv f64fmt (ofBits f64fmt 0x4024000000000000) (ofBits f64fmt 0x4032000000000000))
    (hc : c ∈ fmul f64fmt q (ofBits f64fmt 0x412E848000000000)) :
    c = ofBits f64fmt 0x4120F4471C71C71D := by
  have wf := ofBits_wf f64fmt_sane
  have hd := fdiv_mem f64fmt_sane (wf 0x4024000000000000) (wf 0x4032000000000000)
  have e1 : Impl.fdiv f64fmt (ofBits f64fmt 0x4024000000000000)
      (ofBits f64fmt 0x4032000000000000) = ofBits f64fmt 0x3FE1C71C71C71C72 := by decide +kernel
  rw [e1] at hd
  have hq' := det_eq (fdiv_det f64fmt_sane _ _) hd hq (notNaN (by decide +kernel))
  subst hq'
  have hm := fmul_mem f64fmt_sane (wf 0x3FE1C71C71C71C72) (wf 0x412E848000000000)
  have e2 : Impl.fmul f64fmt (ofBits f64fmt 0x3FE1C71C71C71C72)
      (ofBits f64fmt 0x412E848000000000) = ofBits f64fmt 0x4120F4471C71C71D := by decide +kernel
  rw [e2] at hm
  exact det_eq (fmul_det f64fmt_sane _ _) hm hc (notNaN (by decide +kernel))

/-- The binary's value is strictly below R's cutoff (`f64.lt` = 1). -/
theorem below_cutoff :
    flt f64fmt (ofBits f64fmt 0x4120F4471C71C71C) (ofBits f64fmt 0x4120F4471C71C71D) = 1 := by
  rw [← flt_eq]; decide +kernel

/-- On the shipped `calc_cpm_raw`: a cell with count 10 in a sample of library size 18 ends at
555555.5555555555, strictly below every value R's cutoff formula yields for 10 and 18. -/
theorem boundary (x : Input) (H : HostSem) (l : Layout) (s : Store) (inst : ModuleInst)
    (hD : Domain x) (hA : Admissible H x l s inst) (nth : BitVec 32) {i j : Nat} (hi : i < x.n)
    (hj : j < x.m) (hc : x.count i j = 0x4024000000000000)
    (hl : x.libSize j = 0x4032000000000000) :
    CallReturns H s inst "calc_cpm_raw"
      [.i32 (.ofNat 32 l.y), .i32 (.ofNat 32 l.lib), .i32 (.ofNat 32 l.c), .i32 nth]
      fun s' _ => Holds s' (l.cell x i j) (le64 0x4120F4471C71C71C) ∧
        ∀ q ∈ fdiv f64fmt (ofBits f64fmt 0x4024000000000000) (ofBits f64fmt 0x4032000000000000),
        ∀ c ∈ fmul f64fmt q (ofBits f64fmt 0x412E848000000000),
          flt f64fmt (ofBits f64fmt 0x4120F4471C71C71C) c = 1 := by
  obtain ⟨a, he, hok, hm⟩ := claim_holds.2 x H l s inst hD hA nth
  refine ⟨a, he, hok, hm.mono fun o ho => ?_⟩
  cases o with
  | returned s' vs =>
    obtain ⟨_, hcells, _⟩ := ho
    obtain ⟨out, hh, hcpm⟩ := hcells i hi j hj
    rw [hc, hl] at hcpm
    rw [cpmElem_10_18 hcpm] at hh
    exact ⟨hh, fun q hq c hcm => rCutoff_10_18 hq hcm ▸ below_cutoff⟩
  | trapped _ => exact ho

end Subjects.EdgerCpm
