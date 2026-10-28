import Proofs.Spec
import FVA.Proof.Lib
import FVA.Proof.Exec.Instantiate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

noncomputable def ready : Store × ModuleInst :=
  (instantiate 1000 {} Lifted.module []).getD ({}, {})

theorem eq_some_getD {α : Type} (x : Option α) (d : α) (h : x.isSome = true) :
    x = some (x.getD d) := by
  cases x <;> simp_all

theorem ready_eq : instantiate 1000 {} Lifted.module [] = some ready :=
  eq_some_getD _ _ (by decide +kernel)

theorem pair_instance {m : Module} {p : Store × ModuleInst}
    (hm : ImportsMatch {} m []) (h : instantiate 1000 {} m [] = some p)
    (H : HostSem) : Instance m H p.1 p.2 := by
  rcases p with ⟨s, inst⟩
  exact instantiate_sound hm h

theorem ready_instance (H : HostSem) : Instance Lifted.module H ready.1 ready.2 :=
  pair_instance (m := Lifted.module) (p := ready) (by exact List.Forall₂.nil) ready_eq H

def callStore (s : Store) (input : List UInt8) (capacity : Nat) : Store :=
  (s.withBytes 262143 (List.replicate (capacity + 2) 165)).withBytes 131072 input

def arguments (input : List UInt8) (capacity : Nat) : List Val :=
  [.i32 131072, .i32 262144, .i32 (BitVec.ofNat 32 input.length),
    .i32 (BitVec.ofNat 32 capacity)]

def checkPost (input output : List UInt8) (capacity : Nat) (s : Store) : Bool :=
  match s.mems[0]? with
  | none => false
  | some mem =>
    (List.range output.length).map (fun k => mem.byte (262144 + k)) == output &&
    mem.byte 262143 == 165 && mem.byte (262144 + capacity) == 165 &&
    (List.range input.length).map (fun k => mem.byte (131072 + k)) == input

def checkResult (ret : BitVec 32) (es : List AInstr) : Bool :=
  match es with
  | [e] => toVal e == some (.i32 ret)
  | _ => false

theorem checkResult_sound {ret : BitVec 32} {es : List AInstr}
    (h : checkResult ret es = true) : es = vals [.i32 ret] := by
  rcases es with _ | ⟨e, es⟩
  · contradiction
  rcases es with _ | ⟨f, fs⟩
  · have hv : toVal e = some (.i32 ret) := by simpa only [checkResult, beq_iff_eq] using h
    rw [eq_instr_of_toVal hv]
    rfl
  · contradiction

def checkExample (s : Store) (inst : ModuleInst) (input : List UInt8) (capacity : Nat) (ret : BitVec 32)
    (output : List UInt8) (fuel : Nat) : Bool :=
  match s.mems[0]?, (callStore s input capacity).funcs[2]? with
  | some mem, some fi =>
    decide (131072 + input.length ≤ mem.size) &&
    decide (262143 + (capacity + 2) ≤ mem.size) &&
    (inst.exportFunc "LZ4_decompress_safe" == some 2) &&
    (fi.type.params == [.num .i32, .num .i32, .num .i32, .num .i32]) &&
    (match runDet fuel (invokeConfig (callStore s input capacity) 2 (arguments input capacity)) with
    | none => false
    | some final => (checkResult ret final.instrs) && checkPost input output capacity final.store)
  | _, _ => false

theorem checkPost_sound {input output : List UInt8} {capacity : Nat} {s : Store}
    (h : checkPost input output capacity s = true) :
    ∃ mem, s.mems[0]? = some mem ∧
      (List.range output.length).map (fun k => mem.byte (262144 + k)) = output ∧
      mem.byte 262143 = 165 ∧ mem.byte (262144 + capacity) = 165 ∧
      (List.range input.length).map (fun k => mem.byte (131072 + k)) = input := by
  unfold checkPost at h
  split at h
  · contradiction
  · rename_i mem hm
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨mem, hm, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem checkExample_sound {s : Store} {inst : ModuleInst}
    (hinst : ∀ H, Instance Lifted.module H s inst) {input output : List UInt8} {capacity fuel : Nat} {ret : BitVec 32}
    (h : checkExample s inst input capacity ret output fuel = true) : Example input capacity ret output := by
  intro H
  unfold checkExample at h
  split at h
  · rename_i mem fi hm hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hfit1, hfit2⟩, he⟩, hty⟩, hrun⟩ := h
    refine ⟨s, inst, hinst H, ⟨mem, hm, hfit1⟩,
      ⟨mem, hm, hfit2⟩, 2, he, ⟨fi, hf, ?_⟩, ?_⟩
    · rw [hty]
      exact .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))
    · split at hrun
      · contradiction
      · rename_i final hr
        simp only [Bool.and_eq_true, beq_iff_eq] at hrun
        have hr' : runDet fuel (invokeConfig (callStore s input capacity) 2 (arguments input capacity)) =
            some ⟨final.store, final.frame, vals [.i32 ret]⟩ := by
          rw [hr, ← checkResult_sound hrun.1]
        exact must_returned_of_runDet hr' ⟨rfl, checkPost_sound hrun.2⟩
  · contradiction

theorem empty_zero_holds : empty_zero :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 100) (by decide +kernel)

theorem empty_positive_holds : empty_positive :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem no_input_holds : no_input :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem literal_holds : literal :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem overlap_holds : overlap :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem literal_extension_holds : literal_extension :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem match_extension_holds : match_extension :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem zero_offset_holds : zero_offset :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem bad_offset_holds : bad_offset :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem truncated_holds : truncated :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem too_small_holds : too_small :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

theorem shortcut_holds : shortcut :=
  checkExample_sound (s := ready.1) (inst := ready.2) ready_instance (fuel := 2500) (by decide +kernel)

end Proofs
