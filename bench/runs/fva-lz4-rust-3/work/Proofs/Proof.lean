import Proofs.Spec
import FVA.Proof.Lib
import FVA.Proof.Exec.Instantiate

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem zero_input_holds : zero_input := by
  intro s inst src dst cap H hf
  unfold invokeConfig
  wasm_run [hf, Lifted.module, Lifted.func7]
  exact Must.done (o := .returned s [.i32 4294967295]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

/-- A finite certificate checks actual FVA steps and the reviewed traffic predicate. -/
def finished (result : BitVec 32) (out : List UInt8) (c : Config) : Bool :=
  match c.instrs with
  | [.plain (.iconst .w32 n)] =>
      decide (n = result.toNat) && decide (outputBytes c.store out.length = some out)
  | _ => false

def certify (n cap : Nat) (result : BitVec 32) (out : List UInt8) : Nat → Config → Bool
  | 0, _ => false
  | fuel + 1, c => configSafe n cap c && uniqueStep c &&
      match seq c.store c.frame [] c.instrs with
      | .step s f es => certify n cap result out fuel ⟨s, f, es⟩
      | .final => finished result out c
      | _ => false

theorem finished_sound {result : BitVec 32} {out : List UInt8} {c : Config}
    (h : finished result out c = true) :
    c.instrs = vals [.i32 result] ∧ outputBytes c.store out.length = some out := by
  unfold finished at h
  split at h
  · rename_i n he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hn, ho⟩ := h
    exact ⟨by simpa only [vals, List.map_cons, List.map_nil, Val.instr, hn] using he, ho⟩
  · contradiction

theorem final_no_step {H : HostSem} {c d : Config}
    (hu : uniqueStep c = true) (hs : seq c.store c.frame [] c.instrs = .final) :
    ¬ Step H c d := by
  intro hd
  have hc := seq_complete hd [] [] (by simpa only [uniqueStep, List.append_nil] using hu)
  simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append, hs] at hc
  rcases hc with hc | hc <;> cases hc

theorem certify_sound {n cap : Nat} {result : BitVec 32} {out : List UInt8}
    {fuel : Nat} {c : Config} {H : HostSem}
    (h : certify n cap result out fuel c = true) :
    Must H (fun | .returned s vs => vs = [.i32 result] ∧ outputBytes s out.length = some out
                | .trapped _ => False) c ∧
    ∀ d, Steps H c d → configSafe n cap d = true := by
  induction fuel generalizing c with
  | zero => simp [certify] at h
  | succ fuel ih =>
    simp only [certify, Bool.and_eq_true] at h
    obtain ⟨⟨hsafe, hu⟩, h⟩ := h
    cases hs : seq c.store c.frame [] c.instrs with
    | step s f es =>
      simp only [hs] at h
      have hi := ih h
      have hstep : step c = some ⟨s, f, es⟩ := by simp only [step, hs]
      refine ⟨must_of_step hstep hu hi.1, ?_⟩
      intro d hd
      rcases hd.cases_head with he | ⟨e, he, hed⟩
      · exact he ▸ hsafe
      · have heq := step_complete he hstep hu
        exact hi.2 d (heq ▸ hed)
    | final =>
      simp only [hs] at h
      obtain ⟨hv, ho⟩ := finished_sound h
      refine ⟨Must.done (o := .returned c.store [.i32 result]) ⟨rfl, hv⟩ ⟨rfl, ho⟩, ?_⟩
      intro d hd
      rcases hd.cases_head with he | ⟨e, he, _⟩
      · exact he ▸ hsafe
      · exact False.elim (final_no_step hu hs he)
    | br _ _ | ret _ | stuck => simp [hs] at h

noncomputable def sampleCertificate (input : List UInt8) (cap : Nat) (result : BitVec 32)
    (out : List UInt8) (fuel : Nat) (bytes : Nat → UInt8) : Bool :=
  certify input.length cap result out fuel
    (invokeConfig (((runtime bytes).withBytes 262144 (List.replicate cap 0)).withBytes 131072 input) 7 (arguments input cap))

theorem sample_of_certificate {input : List UInt8} {cap : Nat} {result : BitVec 32}
    {out : List UInt8} {fuel : Nat}
    (h : sampleCertificate input cap result out fuel = fun _ => true) :
    Sample input cap result out := by
  intro bytes H
  have hc := certify_sound (H := H) (congrFun h bytes)
  refine ⟨⟨7, ?_, ?_, hc.1⟩, hc.2⟩
  · rfl
  · exact ⟨.wasm (Lifted.module.types[4]?.getD ⟨[], []⟩) allocation.2 Lifted.func7,
      rfl, by simp [Val.HasType, FuncInst.type, arguments, Lifted.module]⟩

noncomputable def initResult : Store × ModuleInst :=
  (instantiate 10000 {} Lifted.module []).getD (runtime (fun _ => 0), allocation.2)
noncomputable def initBytes : Nat → UInt8 :=
  (initResult.1.mems[0]?.getD ({ pages := 32, max := some 32, byte := fun _ => 0 } : MemInst)).byte

theorem fresh_runtime_holds : fresh_runtime := by
  intro H
  have h : instantiate 10000 {} Lifted.module [] = some (runtime initBytes, allocation.2) := by
    kernel_rfl
  exact ⟨initBytes, instantiate_sound (by exact .nil) h⟩

theorem empty_block_holds : empty_block := by
  apply sample_of_certificate (fuel := 300)
  kernel_rfl

theorem hello_block_holds : hello_block := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem extended_literals_holds : extended_literals := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem overlap_one_holds : overlap_one := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem overlap_two_holds : overlap_two := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem extended_match_holds : extended_match := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem fast_overlap_holds : fast_overlap := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem fast_wild_copy_holds : fast_wild_copy := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem truncated_length_holds : truncated_length := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem zero_offset_holds : zero_offset := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem external_offset_holds : external_offset := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem truncated_literals_holds : truncated_literals := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem truncated_offset_holds : truncated_offset := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem small_capacity_holds : small_capacity := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem relaxed_end_holds : relaxed_end := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem wide32_holds : wide32 := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

theorem wide64_holds : wide64 := by
  apply sample_of_certificate (fuel := 5000)
  kernel_rfl

end Proofs
