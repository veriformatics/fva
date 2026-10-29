import Proofs.Initialization

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def runCase (s : Store) (input : List UInt8) (cap : Nat) : Option Config :=
  runDet 2000 (invokeConfig (s.withBytes 131072 input) 7
    [.i32 131072, .i32 1048576, .i32 (BitVec.ofNat 32 input.length),
     .i32 (BitVec.ofNat 32 cap)])

def observed (c : Config) (result : BitVec 32) (output : List UInt8) : Bool :=
  (c.instrs.mapM toVal == some [.i32 result]) &&
  match c.store.mems[0]? with
  | none => false
  | some mem => (List.range output.length).map (fun k => mem.byte (1048576 + k)) == output

noncomputable def checked (s : Store) (input : List UInt8) (cap : Nat)
    (result : BitVec 32) (output : List UInt8) : Bool :=
  match runCase s input cap with
  | none => false
  | some c => observed c result output

theorem mapM_toVal {es : List AInstr} {vs : List Val}
    (h : es.mapM toVal = some vs) : es = vals vs := by
  induction es generalizing vs with
  | nil => simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst vs; rfl
  | cons e es ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs, heq⟩ := h
    subst vs
    rw [eq_instr_of_toVal hv, ih hvs]
    rfl


theorem replay_checked (s : Store) (inst : ModuleInst)
    (hinstance : ∀ H, Instance Lifted.module H s inst)
    (hsize : (s.mems[0]?).map MemInst.size = some 2097152)
    (hexport : inst.exportFunc "lz4_decompress" = some 7)
    (hparam : (s.funcs[7]?).map (fun fi => fi.type.params) =
      some [.num .i32, .num .i32, .num .i32, .num .i32])
    (input : List UInt8) (cap : Nat) (result : BitVec 32)
    (output : List UInt8) (hin : 131072 + input.length ≤ 2097152)
    (hout : 1048576 + cap ≤ 2097152) (h : checked s input cap result output = true) :
    Replay input cap result output := by
  intro H
  refine ⟨s, inst, hinstance H, ?_, ?_, 7, hexport, ?_, ?_⟩
  · obtain ⟨mem, hm, hs⟩ := Option.map_eq_some_iff.mp hsize
    exact ⟨mem, hm, by simpa only [hs] using hin⟩
  · obtain ⟨mem, hm, hs⟩ := Option.map_eq_some_iff.mp hsize
    exact ⟨mem, hm, by simpa only [hs] using hout⟩
  · obtain ⟨fi, hfi, hparams⟩ := Option.map_eq_some_iff.mp hparam
    refine ⟨fi, hfi, ?_⟩
    rw [hparams]
    simp [Val.HasType]
  · unfold checked at h
    cases hr : runCase s input cap with
    | none => simp [hr] at h
    | some c =>
      rw [hr] at h
      have hh := Bool.and_eq_true_iff.mp h
      have hv : c.instrs.mapM toVal = some [.i32 result] := by
        simpa only [observed, beq_iff_eq] using hh.1
      have he := mapM_toVal hv
      have hm : ∃ mem, c.store.mems[0]? = some mem ∧
          (List.range output.length).map (fun k => mem.byte (1048576 + k)) = output := by
        cases hmem : c.store.mems[0]? with
        | none => simp [observed, hmem] at h
        | some mem =>
          refine ⟨mem, rfl, ?_⟩
          simpa only [observed, hmem, beq_iff_eq] using hh.2
      have hc : c = ⟨c.store, c.frame, vals [.i32 result]⟩ := by
        cases c with
        | mk s f es => exact congrArg (fun xs => Config.mk s f xs) he
      rw [hc] at hr
      exact must_returned_of_runDet (n := 2000)
        (c := invokeConfig (s.withBytes 131072 input) 7
          [.i32 131072, .i32 1048576, .i32 (BitVec.ofNat 32 input.length),
           .i32 (BitVec.ofNat 32 cap)])
        (s' := c.store) (f' := c.frame) (vs := [.i32 result]) hr ⟨rfl, hm⟩


end Proofs
