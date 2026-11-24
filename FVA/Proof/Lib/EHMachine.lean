import FVA.Proof.Exec.MachineSys
import FVA.Proof.Lib.EHExamples
import FVA.Proof.Lib.SysExamples

/-!
# Exceptions on the machine (contract U28d E5)

The machine runs U28b's exception examples and the system seams U28g consumes, each as a
kernel-evaluated run equation through the bridges (`machineRun_must`, `machineSegment_sysMust`,
`machineRun_sysMust`):

- `caughtM`: a throw from inside two blocks of a callee leaves both blocks, the callee's label
  and frame (an operand below the call: an administrative step drops it), the `try_table`
  body's label, and the first clause of the enclosing handler catches it: 142, the store + the
  exception; `caughtParam`: the same for every argument `x` (payload `x + 1` kept symbolic);
- `hostCatch`: a host call while a handler is active, then a throw it catches: the process
  returns 42 after one host call;
- `splitCaught`: the run split mid-unwinding (fuel out at an intermediate throw state), the
  segments composed;
- `uncaughtM`: no handler: `Outcome.thrown`, the process abnormal;
- `trapInHandler`, `exitInHandler`: a host trap and `proc_exit` inside a handler are never caught
  (U27's abnormal and exit precedence);
- `tagMaps`: caller and callee name the tag by different indices — the clause resolves in the
  caller's frame, and a local written inside the `try_table` is read after the catch.
-/

namespace FVA.Wasm.Exec.EHMachine

open FVA.Wasm FVA.Wasm.Exec Machine

/-! ## U28b's caught + uncaught calls on the machine -/

/-- U28b's example store as a machine store (no memories). -/
def mstore : MStore := MStore.ofStore EHExamples.store

theorem mstore_inv : mstore.Inv := by
  intro mm hm
  simp [mstore, MStore.ofStore, EHExamples.store] at hm

/-- `main` on the machine: the state where its run stops. -/
def caughtEnd : MState := ((MState.ofInvoke mstore 1 []).runU false 80).1

theorem caughtEnd_ending : caughtEnd.ending = .returned [.i32 142] := by kernel_rfl

theorem caughtEnd_store : caughtEnd.store.abs = EHExamples.thrown 42 := by kernel_rfl

/-- U28b's `caught` through the machine run: 142, the store + exactly its exception. -/
theorem caughtM (H : HostSem) :
    Must H (fun | .returned s vs => s = EHExamples.thrown 42 ∧ vs = [.i32 142] | _ => False)
      (invokeConfig EHExamples.store 1 []) := by
  have habs : (MState.ofInvoke mstore 1 []).abs = invokeConfig EHExamples.store 1 [] := by
    rw [abs_ofInvoke]
    rfl
  rw [← habs]
  exact machineRun_must (m' := caughtEnd) (n := 80)
    (b := ((MState.ofInvoke mstore 1 []).runU false 80).2) mstore_inv rfl
    (abs_returned caughtEnd_ending) ⟨caughtEnd_store, rfl⟩

/-- `uncaught` on the machine: the state where its run stops. -/
def uncaughtEnd : MState := ((MState.ofInvoke mstore 2 []).runU false 40).1

theorem uncaughtEnd_ending : uncaughtEnd.ending = .thrown 0 := by kernel_rfl

theorem uncaughtEnd_store : uncaughtEnd.store.abs = EHExamples.thrown 8 := by kernel_rfl

/-- U28b's `uncaught` through the machine run: `Outcome.thrown`, exception 0 in the store. -/
theorem uncaughtM (H : HostSem) :
    Must H (fun | .thrown s a => s = EHExamples.thrown 8 ∧ a = 0 | _ => False)
      (invokeConfig EHExamples.store 2 []) := by
  have habs : (MState.ofInvoke mstore 2 []).abs = invokeConfig EHExamples.store 2 [] := by
    rw [abs_ofInvoke]
    rfl
  rw [← habs]
  exact machineRun_must (m' := uncaughtEnd) (n := 40)
    (b := ((MState.ofInvoke mstore 2 []).runU false 40).2) mstore_inv rfl
    (abs_thrown uncaughtEnd_ending) ⟨uncaughtEnd_store, rfl⟩

/-! ## A symbolic payload -/

/-- `[i32] → [i32]`. -/
def i32I32 : FuncType := ⟨[.num .i32], [.num .i32]⟩

/-- `mainX x`: `main` with `thrower x`: the payload `x + 1`. -/
def mainXBody : Expr :=
  [.iconst .w32 100,
    .block (.val (.num .i32))
      [.tryTable .empty [.tag 0 0] [.iconst .w32 5, .localGet 0, .call 0, .drop],
        .iconst .w32 0],
    .ibinop .w32 .add]

/-- U28b's store + function 3 = `mainX`. -/
def pmstore : MStore :=
  MStore.ofStore { EHExamples.store with
    funcs := EHExamples.store.funcs ++ [.wasm ⟨[i32I32], 0⟩ EHExamples.inst ⟨0, [], mainXBody⟩] }

theorem pmstore_inv : pmstore.Inv := by
  intro mm hm
  simp [pmstore, MStore.ofStore, EHExamples.store] at hm

/-- The machine has finished with `v : i32` alone. -/
def returnsI32 (m : MState) (v : BitVec 32) : Bool :=
  m.code.isEmpty && m.ctl.isEmpty && match m.stack with
    | [.i32 w] => w == v
    | _ => false

theorem returnsI32_ending {m : MState} {v : BitVec 32} (h : returnsI32 m v = true) :
    m.ending = .returned [.i32 v] := by
  rcases m with ⟨st, f, stk, code, ctl⟩
  simp only [returnsI32, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  match stk, h with
  | [.i32 w], h =>
    have hw : w = v := by simpa using h
    subst hw
    rfl

/-- Every payload byte: the run returns `100 + (x + 1)` (one kernel run per value — a symbolic
`i32` stalls where it crosses the instruction encoding: `toVal`'s `n < 2^32` test on
`(Val.i32 x).instr`; all-input runs = U28g's symbolic method). -/
theorem caughtParam_run : ∀ x < 256,
    returnsI32 ((MState.ofInvoke pmstore 3 [.i32 (BitVec.ofNat 32 x)]).runU false 80).1
      (100 + (BitVec.ofNat 32 x + 1)) = true := by
  decide +kernel

/-- `mainX x` returns `100 + (x + 1)` for every payload byte and every host: the bridge used
under a binder, through caught-throw transfer. -/
theorem caughtParam (H : HostSem) : ∀ x < 256,
    Must H (fun | .returned _ vs => vs = [.i32 (100 + (BitVec.ofNat 32 x + 1))] | _ => False)
      (invokeConfig pmstore.abs 3 [.i32 (BitVec.ofNat 32 x)]) := by
  intro x hx
  rw [← abs_ofInvoke]
  exact machineRun_must (n := 80)
    (b := ((MState.ofInvoke pmstore 3 [.i32 (BitVec.ofNat 32 x)]).runU false 80).2)
    pmstore_inv rfl (abs_returned (returnsI32_ending (caughtParam_run x hx))) rfl

/-! ## Processes: segments, hosts under handlers, traps and exits -/

/-- A process with no host calls. -/
abbrev idleWorld : World where
  St := Unit
  host _ _ _ _ _ _ := False
  exited _ := none
  stay h := h.elim

/-- The caught run split where fuel runs out mid-unwinding (21 steps: the exception just left the
callee's frame, the operand `5` below it — the next step is administrative), then resumed. -/
def splitMid : MState := ((MState.ofInvoke mstore 1 []).runU true 21).1

theorem splitMid_admin : splitMid.admin = true := by decide +kernel

theorem splitEnd_ending : (splitMid.runU true 60).1.ending = .returned [.i32 142] := by
  kernel_rfl

/-- `caughtM` as a process under the granting policy, from two segments composed at an
intermediate throw state. -/
theorem splitCaught :
    SysMust idleWorld true (fun | .returned _ _ vs => vs = [.i32 142] | _ => False)
      ((), invokeConfig EHExamples.store 1 []) := by
  have habs : (MState.ofInvoke mstore 1 []).abs = invokeConfig EHExamples.store 1 [] := by
    rw [abs_ofInvoke]
    rfl
  rw [← habs]
  refine machineSegment_sysMust (m' := splitMid) (n := 21)
    (b := ((MState.ofInvoke mstore 1 []).runU true 21).2) mstore_inv rfl rfl ?_
  have hinv : splitMid.Inv := by
    intro mm hm
    have : splitMid.store.mems = [] := by decide +kernel
    simp [this] at hm
  refine machineSegment_sysMust (m' := (splitMid.runU true 60).1) (n := 60)
    (b := (splitMid.runU true 60).2) hinv rfl rfl ?_
  exact sysMust_returned rfl (abs_returned splitEnd_ending).2 rfl

/-- The uncaught call as a process: it finishes abnormally. -/
theorem uncaughtSysM :
    SysMust idleWorld true (fun | .abnormal _ s => s = EHExamples.thrown 8 | _ => False)
      ((), invokeConfig EHExamples.store 2 []) := by
  have habs : (MState.ofInvoke mstore 2 []).abs = invokeConfig EHExamples.store 2 [] := by
    rw [abs_ofInvoke]
    rfl
  rw [← habs]
  refine machineSegment_sysMust (m' := (MState.ofInvoke mstore 2 []).runU true 40 |>.1) (n := 40)
    (b := ((MState.ofInvoke mstore 2 []).runU true 40).2) mstore_inv rfl rfl ?_
  have hf : Final ((MState.ofInvoke mstore 2 []).runU true 40).1.abs
      (.thrown (EHExamples.thrown 8) 0) := by
    have h := abs_thrown (m := ((MState.ofInvoke mstore 2 []).runU true 40).1) (a := 0)
      (by kernel_rfl)
    have hs : ((MState.ofInvoke mstore 2 []).runU true 40).1.store.abs = EHExamples.thrown 8 := by
      kernel_rfl
    rwa [hs] at h
  exact .done (sysFinal_thrown rfl hf.2) hf.1.symm

/-- `[] → []`, the tag's type here. -/
def unitT : FuncType := ⟨[], []⟩
/-- `[] → [i32]`. -/
def mainT : FuncType := ⟨[], [.num .i32]⟩

/-- Host function 0 (host id 0), module function 1, host function 2 (host id 1); tag 0. -/
def hinst : ModuleInst :=
  { types := [⟨[unitT], 0⟩, ⟨[mainT], 0⟩], funcs := [0, 1, 2], tags := [0] }

/-- A process store running `body` as function 1. -/
def hstore (body : Expr) : MStore where
  base :=
    { tags := [⟨⟨[unitT], 0⟩⟩]
      funcs := [.host ⟨[unitT], 0⟩ 0, .wasm ⟨[mainT], 0⟩ hinst ⟨1, [], body⟩,
        .host ⟨[unitT], 0⟩ 1] }
  mems := []

theorem hstore_inv (body : Expr) : (hstore body).Inv := by
  intro mm hm
  simp [hstore] at hm

/-- Inside a `try_table` with a `catch_all`: host 0, then a throw the clause catches; 42 after
the block. -/
def hostCatchBody : Expr :=
  [.block .empty [.tryTable .empty [.all 0] [.call 0, .throw 0]], .iconst .w32 42]

/-- The host call happens under the handler (`abs_host` through a handler layer), the throw is
caught: the process returns 42 after one host call. -/
theorem hostCatch :
    SysMust SysExamples.exitWorld true
      (fun | .returned σ _ vs => σ = (1, none) ∧ vs = [.i32 42] | _ => False)
      ((0, none), invokeConfig (hstore hostCatchBody).abs 1 []) := by
  rw [← abs_ofInvoke]
  refine machineRun_sysMust (n := 40) SysExamples.exitHost_ok (σ' := (1, none))
    (m' := (sysRun SysExamples.exitWorld.exited SysExamples.exitHost 40 ((0, none),
      MState.ofInvoke (hstore hostCatchBody) 1 [])).2.1)
    (b := (sysRun SysExamples.exitWorld.exited SysExamples.exitHost 40 ((0, none),
      MState.ofInvoke (hstore hostCatchBody) 1 [])).2.2) (hstore_inv _) rfl ?_
  exact sysMust_returned rfl (SysExamples.done42_abs (by decide +kernel)) ⟨rfl, rfl⟩

/-- A trapping host call inside a `try_table` with a `catch_all`: the trap passes the handler. -/
theorem trapInHandler :
    SysMust SysExamples.trapWorld true SysExamples.trapQ
      ((), invokeConfig
        (hstore [.block .empty [.tryTable .empty [.all 0] [.call 0]]]).abs 1 []) := by
  rw [← abs_ofInvoke]
  refine machineRun_sysMust (n := 20) SysExamples.trapHost_ok
    (m' := (sysRun SysExamples.trapWorld.exited SysExamples.trapHost 20 ((),
      MState.ofInvoke (hstore [.block .empty [.tryTable .empty [.all 0] [.call 0]]]) 1 [])).2.1)
    (b := (sysRun SysExamples.trapWorld.exited SysExamples.trapHost 20 ((),
      MState.ofInvoke (hstore [.block .empty [.tryTable .empty [.all 0] [.call 0]]]) 1
        [])).2.2) (hstore_inv _) rfl ?_
  exact sysMust_trap rfl rfl trivial

/-- `proc_exit 7` inside a `try_table` with a `catch_all`: the process exits, the clause never
runs. -/
theorem exitInHandler :
    SysMust SysExamples.exitWorld true SysExamples.exitQ
      ((0, none), invokeConfig (hstore [.call 0,
        .block .empty [.tryTable .empty [.all 0] [.call 2]], .call 0]).abs 1 []) := by
  rw [← abs_ofInvoke]
  refine machineRun_sysMust (n := 30) SysExamples.exitHost_ok (σ' := (1, some 7))
    (m' := (sysRun SysExamples.exitWorld.exited SysExamples.exitHost 30 ((0, none),
      MState.ofInvoke (hstore [.call 0, .block .empty [.tryTable .empty [.all 0] [.call 2]],
        .call 0]) 1 [])).2.1)
    (b := (sysRun SysExamples.exitWorld.exited SysExamples.exitHost 30 ((0, none),
      MState.ofInvoke (hstore [.call 0, .block .empty [.tryTable .empty [.all 0] [.call 2]],
        .call 0]) 1 [])).2.2) (hstore_inv _) rfl ?_
  exact sysMust_exited rfl ⟨rfl, rfl⟩

/-! ## The frame at a handler -/

/-- `[i32] → []`. -/
def i32T : FuncType := ⟨[.num .i32], []⟩

/-- The callee's instance names tag address 0 by index 1. -/
def calleeInst : ModuleInst := { types := [⟨[i32T], 0⟩], funcs := [0], tags := [1, 0] }

/-- The caller's instance names tag address 0 by index 0 and calls the callee. -/
def callerInst : ModuleInst :=
  { types := [⟨[i32T], 0⟩, ⟨[mainT], 0⟩], funcs := [0, 1], tags := [0, 1] }

/-- The caller: local 0 := 9 inside the `try_table`, then `callee 30`; its tag-0 clause branches
with the payload; after the block, payload + local 0. -/
def callerBody : Expr :=
  [.block (.val (.num .i32))
      [.tryTable .empty [.tag 0 0] [.iconst .w32 9, .localSet 0, .iconst .w32 30, .call 0],
        .iconst .w32 0],
    .localGet 0, .ibinop .w32 .add]

/-- Tag addresses 0 and 1 (same type); function 0 = the callee (throws tag index 1 = address 0
with its argument), function 1 = the caller. -/
def tstore : MStore where
  base :=
    { tags := [⟨⟨[i32T], 0⟩⟩, ⟨⟨[i32T], 0⟩⟩]
      funcs := [.wasm ⟨[i32T], 0⟩ calleeInst ⟨0, [], [.localGet 0, .throw 1]⟩,
        .wasm ⟨[mainT], 0⟩ callerInst ⟨1, [(1, .num .i32)], callerBody⟩] }
  mems := []

theorem tstore_inv : tstore.Inv := by
  intro mm hm
  simp [tstore] at hm

/-- The caller's clause resolves its tag index in the caller's frame (address 0 = the callee's
index 1; resolved in the callee's frame it would name address 1 and miss), and the local
written inside the `try_table` survives the catch: 30 + 9. -/
theorem tagMaps (H : HostSem) :
    Must H (fun | .returned _ vs => vs = [.i32 39] | _ => False)
      (invokeConfig tstore.abs 1 []) := by
  rw [← abs_ofInvoke]
  exact machineRun_must (n := 60) (b := ((MState.ofInvoke tstore 1 []).runU false 60).2) tstore_inv
    rfl (abs_returned (returnsI32_ending (by decide +kernel))) rfl

-- contract U28d E5: the standard three axioms alone
#print axioms caughtM
#print axioms caughtParam
#print axioms splitCaught
#print axioms uncaughtSysM
#print axioms hostCatch
#print axioms trapInHandler
#print axioms exitInHandler
#print axioms tagMaps

end FVA.Wasm.Exec.EHMachine
