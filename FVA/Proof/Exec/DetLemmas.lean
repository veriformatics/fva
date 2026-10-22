import FVA.Proof.Exec.Sound

/-! # Canonical values and administrative decomposition for execution proofs -/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

theorem seq_vals (s : Store) (f : Frame) (vs ws : List Val) (es : List AInstr) :
    seq s f vs (vals ws ++ es) = seq s f (ws.reverse ++ vs) es := by
  induction ws generalizing vs with
  | nil => rfl
  | cons w ws ih =>
    simp only [vals, List.map_cons, List.cons_append, seq, toVal_instr]
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem trap_counterexample (H : HostSem) (s : Store) (f : Frame) :
    ∃ c c₁ c₂ : Config,
      Step H c c₁ ∧ step c = some c₂ ∧ c₁ ≠ c₂ := by
  refine ⟨⟨s, f, [.trap, .plain .nop, .plain .nop]⟩,
    ⟨s, f, [.trap, .plain .nop]⟩, ⟨s, f, [.trap]⟩, ?_, rfl, ?_⟩
  · exact Step.seq (vs := []) (rest := [.plain .nop])
      (Step.trap (.seq [] .hole [.plain .nop]) (by simp [EvalCtx.fill]))
  · intro h
    have hh := congrArg Config.instrs h
    cases hh

theorem atInstr_plain_of_step {s f i vs s' f' stk out} (rest : List AInstr)
    (h : instrStep s f i vs = some (s', f', stk, out)) :
    atInstr s f vs (.plain i) rest = .step s' f' (vals stk.reverse ++ out ++ rest) := by
  unfold atInstr
  split <;> try simp_all
  all_goals cases h

theorem stack_take (vs ws : List Val) :
    (vs.reverse ++ ws).take vs.length = vs.reverse := List.take_left' (by simp)

theorem stack_drop (vs ws : List Val) :
    (vs.reverse ++ ws).drop vs.length = ws := List.drop_left' (by simp)

@[simp] theorem seq_values (s : Store) (f : Frame) (stk vs : List Val) :
    seq s f stk (vals vs) = .final := by
  simpa only [List.append_nil, seq] using seq_vals s f stk vs []

theorem seq_block_br (s : Store) (f : Frame) (args : List Val) {l : Nat} (L : BlockCtx l) :
    ∀ (k : Nat) (stk : List Val) (rest : List AInstr),
      ∃ extra, seq s f stk (L.fill (vals args ++ [.plain (.br (l + k))]) ++ rest) =
        .br k (args.reverse ++ extra) := by
  induction L with
  | base vs tail =>
    intro k stk rest
    refine ⟨vs.reverse ++ stk, ?_⟩
    simp only [BlockCtx.fill, Nat.zero_add, List.append_assoc, seq_vals,
      List.cons_append, seq, toVal, atInstr]
  | @label l vs n cont inner tail ih =>
    intro k stk rest
    obtain ⟨extra, hx⟩ := ih (k + 1) [] []
    refine ⟨extra, ?_⟩
    have he : l + 1 + k = l + (k + 1) := by omega
    simp only [List.append_nil] at hx
    simp only [BlockCtx.fill, he, List.append_assoc, seq_vals,
      List.cons_append, seq, toVal, atInstr, hx]

theorem seq_block_ret (s : Store) (f : Frame) (args : List Val) {l : Nat} (L : BlockCtx l) :
    ∀ (stk : List Val) (rest : List AInstr),
      ∃ extra, seq s f stk (L.fill (vals args ++ [.plain .return_]) ++ rest) =
        .ret (args.reverse ++ extra) := by
  induction L with
  | base vs tail =>
    intro stk rest
    refine ⟨vs.reverse ++ stk, ?_⟩
    simp only [BlockCtx.fill, List.append_assoc, seq_vals,
      List.cons_append, seq, toVal, atInstr]
  | label vs n cont inner tail ih =>
    intro stk rest
    obtain ⟨extra, hx⟩ := ih [] []
    refine ⟨extra, ?_⟩
    simp only [List.append_nil] at hx
    simp only [BlockCtx.fill, List.append_assoc, seq_vals,
      List.cons_append, seq, toVal, atInstr, hx]

open FVA.Wasm.Num

private theorem withSign_wf {F : FloatFormat} {z : FVal} (hz : z.WF F) (s : Bool) :
    (z.withSign s).WF F := by
  cases z <;> exact hz

private theorem funop_wf {F : FloatFormat} (hF : F.Sane) {z r : FVal} (hz : z.WF F)
    (op : FUnOp) (hr : r ∈ funop F op z) : r.WF F := by
  cases op <;> dsimp only [funop, fsqrt, fceil, ffloor, ftrunc, fnearest] at hr
  all_goals repeat' split at hr
  all_goals first
    | exact (nans_wf hF hr).1
    | exact ieee_wf hF hr
    | exact hr.1
    | obtain rfl := Set.mem_singleton_iff.1 hr
      first | exact hz | exact withSign_wf hz _ | trivial | exact Nat.two_pow_pos _

private theorem fbinop_wf {F : FloatFormat} (hF : F.Sane) {a b r : FVal}
    (ha : a.WF F) (hb : b.WF F) (op : FBinOp) (hr : r ∈ fbinop F op a b) : r.WF F := by
  cases op <;> dsimp only [fbinop, fadd, fsub, fmul, fdiv, fmin, fmax] at hr
  all_goals repeat' split at hr
  all_goals first
    | exact (nans_wf hF hr).1
    | exact ieee_wf hF hr
    | obtain rfl := Set.mem_singleton_iff.1 hr
      first
        | exact ha
        | exact hb
        | exact withSign_wf ha _
        | exact withSign_wf hb _
        | trivial
        | exact Nat.two_pow_pos _

private theorem funop_det {F : FloatFormat} (hF : F.Sane) {z : FVal} (hz : z.WF F)
    (op : FUnOp) : Det (funop F op z) := by
  cases op with
  | abs | neg => intro v hv w hw _; exact hv.trans hw.symm
  | sqrt => exact fsqrt_det hF z
  | ceil => exact fceil_det hF hz
  | floor => exact ffloor_det hF hz
  | trunc => exact ftrunc_det hF hz
  | nearest => exact fnearest_det hF hz

private theorem fbinop_det {F : FloatFormat} (hF : F.Sane) (a b : FVal)
    (op : FBinOp) : Det (fbinop F op a b) := by
  cases op with
  | add => exact fadd_det hF a b
  | sub => exact fsub_det hF a b
  | mul => exact fmul_det hF a b
  | div => exact fdiv_det hF a b
  | min => exact fmin_det a b
  | max => exact fmax_det a b
  | copysign => intro v hv w hw _; exact hv.trans hw.symm

private theorem float_unique {F : FloatFormat} (hF : F.Sane) {S : Set FVal}
    (hS : Det S) {v w : FVal} (hv : v ∈ S) (hw : w ∈ S) (hvw : v.WF F)
    (hn : Impl.isNaN (ofBits F (fbits F v)) = false) : w = v := by
  rw [ofBits_fbits hF hvw] at hn
  exact (hS v hv w hw (by simpa only [← isNaN_iff, hn] using Bool.false_ne_true)).symm

theorem implUn_unique {F : FloatFormat} (hF : F.Wide) {z r : FVal} (hz : z.WF F)
    (op : FUnOp) (hr : r ∈ funop F op z)
    (hn : Impl.isNaN (ofBits F (fbits F (implUn F op z))) = false) :
    r = implUn F op z :=
  float_unique hF.toSane (funop_det hF.toSane hz op) (implUn_mem hF hz op) hr
    (funop_wf hF.toSane hz op (implUn_mem hF hz op)) hn

theorem implBin_unique {F : FloatFormat} (hF : F.Sane) {a b r : FVal}
    (ha : a.WF F) (hb : b.WF F) (op : FBinOp) (hr : r ∈ fbinop F op a b)
    (hn : Impl.isNaN (ofBits F (fbits F (implBin F op a b))) = false) :
    r = implBin F op a b :=
  float_unique hF (fbinop_det hF a b op) (implBin_mem hF ha hb op) hr
    (fbinop_wf hF ha hb op (implBin_mem hF ha hb op)) hn

theorem implConvert_unique {F : FloatFormat} (hF : F.Sane) {M : Nat} (i : BitVec M)
    (sx : Sx) {r : FVal} (hr : r ∈ convertFrom F sx i)
    (hn : Impl.isNaN (ofBits F (fbits F (implConvert F sx i))) = false) :
    r = implConvert F sx i := by
  cases sx with
  | u =>
    exact float_unique hF (fconvertU_det hF i) (fconvertU_mem hF i) hr
      (ieee_wf hF (fconvertU_mem hF i)) hn
  | s =>
    exact float_unique hF (fconvertS_det hF i) (fconvertS_mem hF i) hr
      (ieee_wf hF (fconvertS_mem hF i)) hn

private theorem fpromote_wf {z r : FVal} (hr : r ∈ fpromote z) : r.WF f64fmt := by
  unfold fpromote at hr
  repeat' split at hr
  all_goals first
    | exact (nans_wf f64fmt_sane hr).1
    | exact hr.1
    | have he := Set.mem_singleton_iff.1 hr
      subst r
      cases z <;> simp_all [FVal.IsInf, FVal.WF]

private theorem fdemote_wf {z r : FVal} (hr : r ∈ fdemote z) : r.WF f32fmt := by
  unfold fdemote at hr
  repeat' split at hr
  all_goals first
    | exact (nans_wf f32fmt_sane hr).1
    | exact ieee_wf f32fmt_sane hr
    | have he := Set.mem_singleton_iff.1 hr
      subst r
      cases z with
      | subnormal s m => cases m <;> simp_all [FVal.IsInf, FVal.IsZero, FVal.WF]
      | _ => simp_all [FVal.IsInf, FVal.IsZero, FVal.WF]

theorem implPromote_unique {z r : FVal} (hz : z.WF f32fmt) (hr : r ∈ fpromote z)
    (hn : Impl.isNaN (ofBits f64fmt (fbits f64fmt (Impl.fpromote z))) = false) :
    r = Impl.fpromote z :=
  float_unique f64fmt_sane (fpromote_det z) (fpromote_mem hz) hr
    (fpromote_wf (fpromote_mem hz)) hn

theorem implDemote_unique {z r : FVal} (hz : z.WF f64fmt) (hr : r ∈ fdemote z)
    (hn : Impl.isNaN (ofBits f32fmt (fbits f32fmt (Impl.fdemote z))) = false) :
    r = Impl.fdemote z :=
  float_unique f32fmt_sane (fdemote_det z) (fdemote_mem hz) hr
    (fdemote_wf (fdemote_mem hz)) hn

theorem num_toVal_none {i : Instr} {args : List Val} {r : Option Val}
    (hr : r ∈ numResults i args) : toVal (.plain i) = none := by
  unfold numResults at hr
  split at hr <;> first | contradiction | rfl

end FVA.Wasm.Exec.Ref
