import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- Select a nested block/loop or the indicated arm of an if. -/
def child (xs : List Instr) (n : Nat) (otherwise : Bool := false) : List Instr :=
  match xs[n]? with
  | some (.block _ b) | some (.loop _ b) => b
  | some (.if_ _ t e) => if otherwise then e else t
  | _ => []

/-- The actual cell-update instructions, through f64.store, in calc_cpm_raw.
    Only this straight-line fragment is the subject of the execution claims below. -/
noncomputable def rawCell : List Instr :=
  (child (child (child (child (child (child Lifted.func86.body 14) 0) 3) 16) 18) 3 true).take 13

/-- Little-endian binary64 bits, without conversion through a host float. -/
def le64 (x : Nat) : List UInt8 := (List.range 8).map (fun k => UInt8.ofNat (x / 256 ^ k))

/-- One page, count at address 0, library size at address 16. -/
def cellStore (c l : Nat) : Store :=
  { mems := [(({ pages := 1, max := none, byte := fun _ => 0 } : MemInst).withBytes
      0 (le64 c)).withBytes 16 (le64 l)] }

/-- At entry to the update: local 0 = column 0; local 5 = output address 0;
    local 11 = library-row address 16. -/
noncomputable def cellStart (c l : Nat) : Config :=
  { store := cellStore c l
    frame := { locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                          .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 16]
               inst := { mems := [0] } }
    instrs := rawCell.map AInstr.plain }

/-- The fragment terminates without a trap and writes these exact bits at address 0. -/
def wrote (bits : Nat) : Outcome → Prop
  | .returned s vs => vs = [] ∧ ∃ m, s.mems[0]? = some m ∧ m.read 0 8 = bits
  | .trapped _ => False

/-- Binding to the shipped artifact: export 160 is defined function 86 (74 function
    imports), and its extracted update multiplies by 1e6 before dividing. -/
def artifact_binding : Prop :=
  Lifted.module.exports.any (fun e => e.name == "calc_cpm_raw" &&
    match e.desc with | .func n => n == 160 | _ => false) = true ∧
  (Lifted.module.imports.filter (fun i => match i.desc with | .func _ => true | _ => false)).length = 74 ∧
  Lifted.module.funcs[86]? = some Lifted.func86 ∧
  rawCell = [.localGet 5, .localGet 5, .load .f64 ⟨3, 0⟩,
    .fconst .w64 4696837146684686336, .fbinop .w64 .mul,
    .localGet 11, .localGet 0, .iconst .w32 3, .ibinop .w32 .shl,
    .ibinop .w32 .add, .load .f64 ⟨3, 0⟩, .fbinop .w64 .div, .store .f64 ⟨3, 0⟩]

/-- R1 counterexample arithmetic on the actual update fragment: finite positive
    c = L = 2^1023 (bits 0x7fe0000000000000) writes positive infinity.
    Full-function reachability is demonstrated separately by the runtime harness. -/
def r1_overflow : Prop := artifact_binding ∧
  ∀ H : HostSem, Must H (wrote 9218868437227405312)
    (cellStart 9214364837600034816 9214364837600034816)

/-- R2 boundary arithmetic on the actual update fragment: c=10, L=18 writes
    0x4120f4471c71c71c. The documented cutoff computed by R is one ulp higher.
    The R filtering decision is demonstrated by verification/filter.R. -/
def r2_boundary : Prop := artifact_binding ∧
  ∀ H : HostSem, Must H (wrote 4693019397977130780)
    (cellStart 4621819117588971520 4625759767262920704)

end Proofs
