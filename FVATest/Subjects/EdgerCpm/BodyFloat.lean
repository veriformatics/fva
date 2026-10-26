import FVATest.Subjects.EdgerCpm.BodyContext
import FVA.Proof.Numerics.Total

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

theorem mul_wf {F : FloatFormat} (hF : F.Sane) {a b z : FVal}
    (h : z ∈ fmul F a b) : z.WF F := by
  unfold fmul at h
  repeat' split at h
  all_goals first
    | exact (nans_wf hF h).1
    | exact ieee_wf hF h
    | obtain rfl := Set.mem_singleton_iff.mp h
      first | trivial | exact Nat.two_pow_pos _

theorem div_wf {F : FloatFormat} (hF : F.Sane) {a b z : FVal}
    (h : z ∈ fdiv F a b) : z.WF F := by
  unfold fdiv at h
  repeat' split at h
  all_goals first
    | exact (nans_wf hF h).1
    | exact ieee_wf hF h
    | obtain rfl := Set.mem_singleton_iff.mp h
      first | trivial | exact Nat.two_pow_pos _

theorem must_mul64_context {H : HostSem} {Q : Outcome → Prop} {s : Store} {f : Frame}
    {es : List AInstr} (C : Context) (a b : BitVec 64)
    (hfoc : seqFocus (NumAt (.fbinop .w64 .mul) 2 [.f64 a, .f64 b]) [] es)
    (hk : ∀ z, ofBits f64fmt z ∈ fmul f64fmt (ofBits f64fmt a) (ofBits f64fmt b) →
      Must H Q (C.fill ⟨s, f, seqPlug 2 (vals [.f64 z]) [] es⟩)) :
    Must H Q (C.fill ⟨s, f, es⟩) := by
  apply must_fbinop_context C hfoc
  · obtain ⟨z, hz⟩ := fmul_nonempty f64fmt_sane
      (ofBits_wf f64fmt_sane a) (ofBits_wf f64fmt_sane b)
    exact ⟨r64 z, z, hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    apply hk (fbits f64fmt z)
    rw [ofBits_fbits f64fmt_sane (mul_wf f64fmt_sane hz)]
    exact hz

theorem must_div64_context {H : HostSem} {Q : Outcome → Prop} {s : Store} {f : Frame}
    {es : List AInstr} (C : Context) (a b : BitVec 64)
    (hfoc : seqFocus (NumAt (.fbinop .w64 .div) 2 [.f64 a, .f64 b]) [] es)
    (hk : ∀ z, ofBits f64fmt z ∈ fdiv f64fmt (ofBits f64fmt a) (ofBits f64fmt b) →
      Must H Q (C.fill ⟨s, f, seqPlug 2 (vals [.f64 z]) [] es⟩)) :
    Must H Q (C.fill ⟨s, f, es⟩) := by
  apply must_fbinop_context C hfoc
  · obtain ⟨z, hz⟩ := fdiv_nonempty f64fmt_sane
      (ofBits_wf f64fmt_sane a) (ofBits_wf f64fmt_sane b)
    exact ⟨r64 z, z, hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    apply hk (fbits f64fmt z)
    rw [ofBits_fbits f64fmt_sane (div_wf f64fmt_sane hz)]
    exact hz

end Subjects.EdgerCpm.Body
