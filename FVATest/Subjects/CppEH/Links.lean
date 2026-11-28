import FVATest.Subjects.CppEH.Seams
import FVATest.Subjects.CppEH.Spec
import FVATest.Subjects.CppEH.Lifted
import FVA.Proof.Wasi.Canonical

/-! Seam links of `eh` (contract U28g F2): each takes the twin's seam-start state `T` as a
variable with its facts and transfers `SysMust` from the patched seam end back to the patched
seam start (`machineRun_sysMust` over the seam's run + `Eqv` to the twin's end, patched). -/

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasm.Exec.Machine.Oblivious FVA.Wasi
  FVA.Wasm.Num

namespace Subjects.CppEH

noncomputable abbrev md : Module := Lifted.module

noncomputable abbrev Wd : World := (world md 0).restrict (E md 0)

noncomputable abbrev Xh := wasiHost md 0 none

theorem start_exited : State.exited start = none := rfl

/-! ## Patches -/

/-- eh's local 0 + the wrapper's local 0. -/
def ps1 : List (Option Pos) := [some (.top 0), some (.loc 2 0)]
/-- The wrapper's local 0 + the result saved in the wrapper frame's entry. -/
def ps2 : List (Option Pos) := [some (.loc 2 0), some (.saved 2 0)]
/-- The payload bytes. -/
def pb : List (Option Pos) :=
  [some (.byte 0 70448), some (.byte 0 70449), some (.byte 0 70450), some (.byte 0 70451)]

/-- The wrapper's local 0 alone (eh's local 0 overwritten). -/
def psL : List (Option Pos) := [none, some (.loc 2 0)]
/-- Two slot values. -/
def vv (a b : BitVec 32) : List TVal := [.val (.i32 a), .val (.i32 b)]
/-- The little-endian bytes of `x`. -/
def vb (x : BitVec 32) : List TVal :=
  [.byte (x.toNat % 256), .byte (x.toNat / 256 % 256), .byte (x.toNat / 65536 % 256),
    .byte (x.toNat / 16777216 % 256)]

/-- Patches touching memory bytes alone. -/
def ByteOnly (ts : List (Pos × TVal)) : Prop := ∀ t ∈ ts, ∃ mi a b, t = (.byte mi a, .byte b)

theorem putMems_append (a b : List (Pos × TVal)) (ms : List MMem) :
    putMems (a ++ b) ms = putMems b (putMems a ms) := by
  induction a generalizing ms with
  | nil => rfl
  | cons t a ih => obtain ⟨p, v⟩ := t; cases p <;> cases v <;> simp [putMems, ih]

theorem putLocals_append (a b : List (Pos × TVal)) (L : List (Option Val)) :
    putLocals (a ++ b) L = putLocals b (putLocals a L) := by
  induction a generalizing L with
  | nil => rfl
  | cons t a ih => obtain ⟨p, v⟩ := t; cases p <;> cases v <;> simp [putLocals, ih]

theorem putCtl_append (a b : List (Pos × TVal)) (K : List Ctl) :
    putCtl (a ++ b) K = putCtl b (putCtl a K) := by
  induction a generalizing K with
  | nil => rfl
  | cons t a ih => obtain ⟨p, v⟩ := t; cases p <;> cases v <;> simp [putCtl, ih]

theorem putLocals_byteOnly {ts : List (Pos × TVal)} (h : ByteOnly ts) (L : List (Option Val)) :
    putLocals ts L = L := by
  induction ts generalizing L with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨mi, a, b, rfl⟩ := h t (List.mem_cons_self ..)
    exact ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) L

theorem putCtl_byteOnly {ts : List (Pos × TVal)} (h : ByteOnly ts) (K : List Ctl) :
    putCtl ts K = K := by
  induction ts generalizing K with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨mi, a, b, rfl⟩ := h t (List.mem_cons_self ..)
    exact ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) K

theorem byteOnly_pb (x : BitVec 32) : ByteOnly (ride pb (vb x)) := by
  intro t ht; simp only [ride, pb, vb, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩

theorem byteOnly_nil : ByteOnly [] := fun _ h => absurd h List.not_mem_nil

theorem memEqv_list_refl : ∀ l : List MMem, List.Forall₂ MemEqv l l
  | [] => .nil
  | a :: l => .cons (memEqv_refl a) (memEqv_list_refl l)

theorem sysMust_of_eqv {W : World} {fits : Bool} {Q : SysOutcome W.St → Prop} {σ : W.St}
    {P P' : MState} (h : Eqv P P') (hend : SysMust W fits Q (σ, P'.abs)) :
    SysMust W fits Q (σ, P.abs) := by
  rw [eqv_abs h]; exact hend

theorem wd_exited : Wd.exited = State.exited := rfl

/-- The seam step of every link: a run of the patched start to `R`, `R` alike the patched
twin end. -/
theorem seam {Q : SysOutcome State → Prop} {n : Nat} {σ : State} {P R P' : MState} (hi : P.Inv)
    (hrun : sysRun State.exited Xh n (σ, P) = (σ, R, true)) (heqv : Eqv R P')
    (hend : SysMust Wd true Q (σ, P'.abs)) : SysMust Wd true Q (σ, P.abs) :=
  machineRun_sysMust (W := Wd) (wasiHost_ok md 0) n hi hrun (sysMust_of_eqv heqv hend)

theorem ride_append : ∀ (p q : List (Option Pos)) (v w : List TVal), p.length = v.length →
    ride (p ++ q) (v ++ w) = ride p v ++ ride q w
  | [], _, [], _, _ => rfl
  | some _ :: p, q, _ :: v, w, h => by
    simp only [List.cons_append, ride, List.cons_append, ride_append p q v w (by simpa using h)]
  | none :: p, q, _ :: v, w, h => by
    simp only [List.cons_append, ride, ride_append p q v w (by simpa using h)]
  | [], _, _ :: _, _, h | _ :: _, _, [], _, h => by simp at h

theorem bytesOK_slots {a : List (Pos × TVal)} {tb : List (Pos × TVal)} {ms : List MMem}
    (ha : ∀ t ∈ a, ∀ mi x, t.1 ≠ .byte mi x) (h : BytesOK tb ms) : BytesOK (a ++ tb) ms := by
  intro mi x b hm
  rcases List.mem_append.mp hm with hm | hm
  · exact absurd rfl (ha _ hm mi x)
  · exact h mi x b hm

theorem slots_ps1 (a b : BitVec 32) : ∀ t ∈ ride ps1 (vv a b), ∀ mi x, t.1 ≠ .byte mi x := by
  intro t ht mi x; simp only [ride, ps1, vv, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp

theorem slots_ps2 (a b : BitVec 32) : ∀ t ∈ ride ps2 (vv a b), ∀ mi x, t.1 ≠ .byte mi x := by
  intro t ht mi x; simp only [ride, ps2, vv, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp

theorem slots_psL (a b : BitVec 32) : ∀ t ∈ ride psL (vv a b), ∀ mi x, t.1 ≠ .byte mi x := by
  intro t ht mi x; simp only [ride, psL, vv, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht; simp

/-- The patch simp set. -/
macro "patch_simp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [put_eq, putMems_append, putLocals_append, putCtl_append, putMems, putLocals,
    putCtl, ride, ps1, ps2, psL, vv, modifyAt, ctlAt, setCallerLocal, setSaved, MStore.abs,
    memEqv_list_refl, memEqv_refl, $hs,*])

/-! ## Links -/

/-- S1a: the launch to F0's start (the input on the operand stack → eh's + the wrapper's
local 0). -/
theorem linkG1 {Q : SysOutcome State → Prop} (x x0 : BitVec 32) {S : MStore} {dtW dtE : DefType}
    {IW IE : ModuleInst} {cW cE : Func}
    (hfW : S.base.funcs[133]? = some (.wasm dtW IW cW))
    (htW : dtW.expand = some ⟨[.num .i32], [.num .i32]⟩) (hdW : cW.localDefaults = [])
    (hbW : cW.body = [.localGet 0, .call 7, .call 132]) (hiW : IW.funcs[7]? = some 7)
    (hfE : S.base.funcs[7]? = some (.wasm dtE IE cE))
    (htE : dtE.expand = some ⟨[.num .i32], [.num .i32]⟩)
    (hdE : cE.localDefaults = [some (.i32 0), some (.i32 0), some (.ref .null)]) (hSi : S.Inv)
    {T : MState}
    (hT : sysRun State.exited Xh 5 (start, MState.ofInvoke S 133 [.i32 x0]) = (start, T, true))
    (hend : SysMust Wd true Q (start, (put (ride ps1 (vv x x)) T).abs)) :
    SysMust Wd true Q (start, (MState.ofInvoke S 133 [.i32 x]).abs) := by
  have h0 := runG1 (X := Xh) (x := x0) start_exited hfW htW hdW hbW hiW hfE htE hdE
  rw [hT] at h0; simp only [Prod.mk.injEq, true_and, and_true] at h0; subst h0
  refine seam hSi (runG1 (X := Xh) (x := x) start_exited hfW htW hdW hbW hiW hfE htE hdE) ?_ hend
  rw [eqv_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> patch_simp []

/-- S1c: the parity test; the input's parity = the twin's. -/
theorem linkG2 {Q : SysOutcome State → Prop} (x x0 : BitVec 32) (hp : x.toNat % 2 = x0.toNat % 2)
    {T T' : MState} {C : List AInstr} {L : List (Option Val)}
    (hc : T.code = .plain (.localGet 0) :: .plain (.iconst .w32 1) ::
      .plain (.ibinop .w32 .and) :: C)
    (hs : T.stack = []) (hl : T.frame.locals = some (.i32 x0) :: L) (hTi : T.Inv)
    (hT' : sysRun State.exited Xh 4 (start, T) = (start, T', true))
    (hend : SysMust Wd true Q (start, (put (ride ps1 (vv x x)) T').abs)) :
    SysMust Wd true Q (start, (put (ride ps1 (vv x x)) T).abs) := by
  have h0 := runG2 (X := Xh) start_exited hc hs hl (r := iand x0 (BitVec.ofNat 32 1)) rfl
  rw [hT'] at h0; simp only [Prod.mk.injEq, true_and, and_true] at h0; subst h0
  have hpar : iand x (BitVec.ofNat 32 1) = iand x0 (BitVec.ofNat 32 1) := by
    simp only [iand]; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and, Nat.and_one_is_mod, hp]
  refine seam (put_inv hTi (by simp [BytesOK, ride, ps1, vv]))
    (runG2 (X := Xh) (M := put (ride ps1 (vv x x)) T) (L := L) (v := x) start_exited
      (by simp only [put_eq]; exact hc) (by simp only [put_eq]; exact hs)
      (by simp [put_eq, ride, ps1, vv, putLocals, hl]) (r := iand x (BitVec.ofNat 32 1)) rfl)
    ?_ hend
  rw [eqv_iff, hpar]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> patch_simp []

/-- S2: the input stored at the payload. -/
theorem linkG3 {Q : SysOutcome State → Prop} (x : BitVec 32) {T T' : MState}
    {C : List AInstr} {L : List (Option Val)} {mm : MMem}
    (hc : T.code = .plain (.localGet 0) :: .plain (.store .i32 ⟨2, 0⟩) :: C)
    (hs : T.stack = [.i32 70448]) (hl : T.frame.locals = some (.i32 1) :: L)
    (hI : T.frame.inst.mems = [0]) (hm : T.store.mems = [mm]) (hb : 70452 ≤ mm.size)
    (hTi : T.Inv) (hT' : sysRun State.exited Xh 3 (start, T) = (start, T', true))
    (hend : SysMust Wd true Q (start, (put (ride ps1 (vv x x) ++ ride pb (vb x)) T').abs)) :
    SysMust Wd true Q (start, (put (ride ps1 (vv x x)) T).abs) := by
  have hmi : mm.Inv := hTi mm (by rw [hm]; exact List.mem_singleton_self _)
  have h0 := runG3 (X := Xh) start_exited hc hs hl hI hm hb
  rw [hT'] at h0; simp only [Prod.mk.injEq, true_and, and_true] at h0; subst h0
  refine seam (put_inv hTi (by simp [BytesOK, ride, ps1, vv]))
    (runG3 (X := Xh) (M := put (ride ps1 (vv x x)) T) (L := L) (v := x) start_exited
      (by simp only [put_eq]; exact hc) (by simp only [put_eq]; exact hs)
      (by simp [put_eq, ride, ps1, vv, putLocals, hl]) (by simp only [put_eq]; exact hI)
      (by simp [put_eq, ride, ps1, vv, putMems, hm]) hb) ?_ hend
  rw [eqv_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · patch_simp [pb, vb, hm]
    exact memEqv_patch4 hmi (by omega) _ _
  all_goals patch_simp [pb, vb, hm]

/-- S3: the payload read back into eh's local 0. -/
theorem linkG4 {Q : SysOutcome State → Prop} (x : BitVec 32) {σ : State}
    (he : State.exited σ = none) {T T' : MState} {C : List AInstr} {w : Option Val}
    {L : List (Option Val)} {mm : MMem}
    (hc : T.code = .plain (.load .i32 ⟨2, 0⟩) :: .plain (.localSet 0) :: C)
    (hs : T.stack = [.i32 70448]) (hl : T.frame.locals = w :: L) (hI : T.frame.inst.mems = [0])
    (hm : T.store.mems = [mm]) (hb : 70452 ≤ mm.size) (hr : mm.read 70448 4 = 1) (hTi : T.Inv)
    (hT' : sysRun State.exited Xh 2 (σ, T) = (σ, T', true))
    (hend : SysMust Wd true Q (σ, (put (ride ps1 (vv x x) ++ ride pb (vb x)) T').abs)) :
    SysMust Wd true Q (σ, (put (ride psL (vv x x) ++ ride pb (vb x)) T).abs) := by
  have hmi : mm.Inv := hTi mm (by rw [hm]; exact List.mem_singleton_self _)
  have h0 := runG4 (X := Xh) he hc hs hl hI hm hb hr
  rw [hT'] at h0; simp only [Prod.mk.injEq, true_and, and_true] at h0; subst h0
  have hk : 70448 + 4 ≤ 2 ^ (mm.depth + W) := by
    have := hmi.2.1; simp only [MMem.Cover, MMem.size] at this hb; omega
  have h256 : ∀ n : Nat, n % 256 < 256 := fun n => Nat.mod_lt _ (by norm_num)
  have hm' : (put (ride psL (vv x x) ++ ride pb (vb x)) T).store.mems =
      [patch4 mm 70448 (x.toNat % 256) (x.toNat / 256 % 256) (x.toNat / 65536 % 256)
        (x.toNat / 16777216 % 256)] := by
    patch_simp [pb, vb, hm, patch4]
  have hb' : 70452 ≤ (patch4 mm 70448 (x.toNat % 256) (x.toNat / 256 % 256)
      (x.toNat / 65536 % 256) (x.toNat / 16777216 % 256)).size := by
    simp only [MMem.size, (patch4_fields ..).1]; exact hb
  have hr' : (patch4 mm 70448 (x.toNat % 256) (x.toNat / 256 % 256) (x.toNat / 65536 % 256)
      (x.toNat / 16777216 % 256)).read 70448 4 = x.toNat := by
    rw [read_patch4 hmi.1 hk (h256 _) (h256 _) (h256 _) (h256 _)]
    exact bytes32 _ x.isLt
  have hok : BytesOK (ride psL (vv x x) ++ ride pb (vb x)) T.store.mems := by
    refine bytesOK_slots (slots_psL x x) ?_
    intro mi a b hmem
    simp only [ride, pb, vb, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
      Pos.byte.injEq, TVal.byte.injEq] at hmem
    rw [hm]
    rcases hmem with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ |
        ⟨⟨rfl, rfl⟩, rfl⟩ <;>
      exact ⟨h256 _, mm, rfl, by omega⟩
  refine seam (put_inv hTi hok)
    (runG4 (X := Xh) (M := put (ride psL (vv x x) ++ ride pb (vb x)) T) (w := w) (L := L) he
      (by simp only [put_eq]; exact hc) (by simp only [put_eq]; exact hs)
      (by patch_simp [pb, vb, hl]) (by simp only [put_eq]; exact hI) hm' hb' hr') ?_ hend
  rw [eqv_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> patch_simp [pb, vb, hm, hl]

/-- S4a, S4′a: `local.get 0; i32.const k; <op>; local.set 0` — the result into eh's local 0. -/
theorem linkG5 {Q : SysOutcome State → Prop} (x x0 : BitVec 32) {k : Nat} (hk : k < 4294967296)
    {op : IBinOp} {r r0 : BitVec 32} (hop : ibinop op x (BitVec.ofNat 32 k) = some r)
    (hop0 : ibinop op x0 (BitVec.ofNat 32 k) = some r0) {tb : List (Pos × TVal)}
    (htb : ByteOnly tb) {σ : State} (he : State.exited σ = none) {T T' : MState}
    {C : List AInstr} {L : List (Option Val)}
    (hc : T.code = .plain (.localGet 0) :: .plain (.iconst .w32 k) :: .plain (.ibinop .w32 op) ::
      .plain (.localSet 0) :: C)
    (hs : T.stack = []) (hl : T.frame.locals = some (.i32 x0) :: L) (hTi : T.Inv)
    (hok : BytesOK tb T.store.mems) (hT' : sysRun State.exited Xh 6 (σ, T) = (σ, T', true))
    (hend : SysMust Wd true Q (σ, (put (ride ps1 (vv r x) ++ tb) T').abs)) :
    SysMust Wd true Q (σ, (put (ride ps1 (vv x x) ++ tb) T).abs) := by
  have h0 := runG5 (X := Xh) he hk hc hs hl hop0
  rw [hT'] at h0; simp only [Prod.mk.injEq, true_and, and_true] at h0; subst h0
  refine seam (put_inv hTi (bytesOK_slots (slots_ps1 x x) hok))
    (runG5 (X := Xh) (M := put (ride ps1 (vv x x) ++ tb) T) (L := L) he hk
      (by simp only [put_eq]; exact hc) (by simp only [put_eq]; exact hs)
      (by patch_simp [putLocals_byteOnly htb, hl]) hop) ?_ hend
  rw [eqv_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    patch_simp [putLocals_byteOnly htb, putCtl_byteOnly htb, hl]

/-- S4b, S4′b: the result returned to the wrapper, the wrapper's `call 132` + its invoke: the
result saved in the wrapper frame's entry. -/
theorem linkG6 {Q : SysOutcome State → Prop} (x x0 r r0 : BitVec 32) {tb : List (Pos × TVal)}
    (htb : ByteOnly tb) {σ : State} (he : State.exited σ = none) {T T' : MState}
    {L : List (Option Val)} {n₁ n₂ : Nat} {c₁ c₂ : List Instr} {s₁ s₂ : List Val}
    {r₁ r₂ : List AInstr} {IW : ModuleInst} {L3 F0 : Ctl} {a : Nat} {dt : DefType}
    {I : ModuleInst} {cf : Func}
    (hc : T.code = [.plain (.localGet 0), .plain .return_]) (hs : T.stack = [])
    (hl : T.frame.locals = some (.i32 r0) :: L)
    (hk : T.ctl = [.label n₁ c₁ s₁ r₁, .label n₂ c₂ s₂ r₂,
      .frame 1 ⟨[some (.i32 x0)], IW⟩ [] [.plain (.call 132)], L3, F0])
    (hiW : IW.funcs[132]? = some a) (hf : T.store.base.funcs[a]? = some (.wasm dt I cf))
    (ht : dt.expand = some ⟨[], []⟩) (hd : cf.localDefaults = []) (hTi : T.Inv)
    (hok : BytesOK tb T.store.mems) (hT' : sysRun State.exited Xh 5 (σ, T) = (σ, T', true))
    (hend : SysMust Wd true Q (σ, (put (ride ps2 (vv x r) ++ tb) T').abs)) :
    SysMust Wd true Q (σ, (put (ride ps1 (vv r x) ++ tb) T).abs) := by
  have h0 := runG6 (X := Xh) he hc hs hl hk (FW := ⟨[some (.i32 x0)], IW⟩) hiW hf ht hd
  rw [hT'] at h0; simp only [Prod.mk.injEq, true_and, and_true] at h0; subst h0
  refine seam (put_inv hTi (bytesOK_slots (slots_ps1 r x) hok))
    (runG6 (X := Xh) (M := put (ride ps1 (vv r x) ++ tb) T) (L := L) (r := r) he
      (n₁ := n₁) (n₂ := n₂) (c₁ := c₁) (c₂ := c₂) (s₁ := s₁) (s₂ := s₂) (r₁ := r₁) (r₂ := r₂)
      (FW := ⟨[some (.i32 x)], IW⟩) (K := [L3, F0])
      (by simp only [put_eq]; exact hc) (by simp only [put_eq]; exact hs)
      (by patch_simp [putLocals_byteOnly htb, hl]) (by patch_simp [putCtl_byteOnly htb, hk])
      hiW (by simp only [put_eq]; exact hf) ht hd) ?_ hend
  rw [eqv_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    patch_simp [putLocals_byteOnly htb, putCtl_byteOnly htb, hl, hk]

/-- S6: the dtors frame exit and the wrapper's exits: the saved result returned. -/
theorem linkG7 {Q : SysOutcome State → Prop} (x r : BitVec 32) {tb : List (Pos × TVal)}
    (htb : ByteOnly tb) {σ : State} (he : State.exited σ = none) {T : MState}
    {IW : ModuleInst} {x0 r0 : BitVec 32} {FD : Frame}
    (hc : T.code = []) (hs : T.stack = [])
    (hk : T.ctl = [.frame 0 ⟨[some (.i32 x0)], IW⟩ [.i32 r0] [], .label 1 [] [] [],
      .frame 1 FD [] []])
    (hTi : T.Inv) (hok : BytesOK tb T.store.mems)
    (hQ : ∀ s : Store, s.exns = T.store.base.exns → Q (.returned σ s [.i32 r])) :
    SysMust Wd true Q (σ, (put (ride ps2 (vv x r) ++ tb) T).abs) := by
  refine machineRun_sysMust (W := Wd) (wasiHost_ok md 0) 3
    (put_inv hTi (bytesOK_slots (slots_ps2 x r) hok))
    (runG7 (X := Xh) (M := put (ride ps2 (vv x r) ++ tb) T) (v := .i32 r)
      (FW := ⟨[some (.i32 x)], IW⟩) (FD := FD) he
      (by simp only [put_eq]; exact hc) (by simp only [put_eq]; exact hs)
      (by patch_simp [putCtl_byteOnly htb, hk])) ?_
  exact sysMust_returned (by rw [wd_exited]; exact he)
    (by simp [MState.abs, Machine.wrap, vals]) (hQ _ (by rw [put_eq]; rfl))

end Subjects.CppEH
