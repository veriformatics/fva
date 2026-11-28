import FVATest.Subjects.WasiGc.Lifted
import FVA.Spec.Wasi.World

/-!
# GC count of a DNA sequence (claim; contract U29b3)

`gc.wasm` = `gc.c` built by the pinned wasi-sdk 34.0 (`build`): direct WASI preview1 calls and its
own `_start`, no C library. It opens `seq.txt` in its first preopened directory, counts the bases
G and C and the bases A, C, G, T, and writes `<gc> <bases>` and a newline to stdout. The claim fixes
one start: argument `gc.wasm`, no environment, empty stdin, the directory `.` holding `seq.txt`,
the clocks at 0. From it every launch exits with status 0 after writing exactly `report seq`, under
the reviewed WASI model restricted to `E` (in-profile calls return), with fitting growth.
-/

namespace Subjects.WasiGc

open FVA.Wasm FVA.Wasm.Exec FVA.Wasi

/-- ASCII text as bytes. -/
def ascii (s : String) : Bytes := s.toList.map fun c => c.toNat.toUInt8

/-- The input file `seq.txt`. -/
def seq : Bytes := ascii "ACGTGGCCAT\nGATTACA\n"

/-- `n` in decimal digits. -/
def decimal (n : Nat) : Bytes := ascii (toString n)

/-- The expected output for the bytes `s`: the count of `G` and `C`, a space, the count of `A`,
`C`, `G` and `T`, a newline. -/
def report (s : Bytes) : Bytes :=
  decimal (s.countP (· ∈ ascii "GC")) ++ ascii " " ++ decimal (s.countP (· ∈ ascii "ACGT")) ++
    ascii "\n"

/-- The process start: argument `gc.wasm`, no environment, empty stdin, the preopened directory
`.` holding `seq.txt`, every clock at 0. -/
def start : State :=
  State.init [ascii "gc.wasm"] [] [] [(ascii ".", .dir [(ascii "seq.txt", .file seq)])] [0, 0, 0, 0]

/-- The command launches at `_start`; from `start`, every launch exits with status 0, and its
stdout is exactly `report seq`. -/
@[fva_claim] def countsGC : Prop :=
  (∃ c mem, Launch Lifted.module "_start" [] c mem) ∧
    ∀ c mem, Launch Lifted.module "_start" [] c mem →
      SysMust ((world Lifted.module mem).restrict (E Lifted.module mem)) true
        (fun o => ∃ τ s, o = .exited τ s 0 ∧ τ.stdout = report seq) (start, c)

end Subjects.WasiGc
