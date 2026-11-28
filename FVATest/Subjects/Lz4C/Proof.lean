import FVATest.Subjects.Lz4C.Top
import FVATest.Subjects.Lz4C.Cut.Entry
import FVATest.Subjects.Lz4C.Cut.ErrRet
import FVATest.Subjects.Lz4C.Cut.ExtB
import FVATest.Subjects.Lz4C.Eval.Accept
import FVATest.Subjects.Lz4C.Accept
import FVA.Proof.Lib.Witness
import FVA.Spec.Exec.System

/-! R1–R3 (`Spec.lean`) on the shipped `lz4-c.wasm`: `Top`'s composition of the cutpoint proofs
(`Cut/*` by stepping, `Eval/*` by engine C). Proof side; never read. -/

namespace Subjects.Lz4C

theorem r1_holds : r1 := r1_iff.mpr <|
  Top.r1_of Cut.entry Eval.s5 Cut.segA Eval.segB Eval.segC Eval.segD Cut.errRet

theorem r2_holds : r2 := r2_iff.mpr <|
  Top.r2_of Cut.entry Eval.s5 Cut.segA Eval.segB Eval.segC Eval.segD Cut.errRet

theorem r3_holds : r3 := r3_iff.mpr <|
  Top.r3_of Cut.entry Eval.s5 Cut.segA Eval.segB Eval.segC Eval.segD Cut.errRet

/-! Input-domain witnesses (U37): the spec's empty block `00` into an empty destination
(`Accept.empty`); `fva trust` checks each against its claim's obligation. -/

open FVA.Wasm.Exec

private theorem emptyBuffers :
    Buffers Accept.empty.src Accept.empty.dst Accept.empty.input Accept.empty.initDst := by
  dsimp [Accept.empty, Buffers]; decide

private theorem emptyPrepared (H : HostSem) :
    Prepared Lifted.module H [.write Accept.empty.src Accept.empty.input,
      .write Accept.empty.dst Accept.empty.initDst] Accept.empty.store alloc.2 :=
  Accept.empty.prepared Accept.empty_prep H

@[fva_witness r1] theorem r1_domain : fva_obligation% r1 :=
  ⟨⟨⟨_, _, _, _, emptyBuffers, NoHost, trivial⟩, ⟨_, _, _, _, emptyBuffers, NoHost, _, _,
    emptyPrepared NoHost⟩⟩, ⟨_, _, _, _, emptyBuffers, NoHost, _, _, emptyPrepared NoHost⟩⟩

@[fva_witness r2] theorem r2_domain : fva_obligation% r2 :=
  ⟨⟨_, _, _, _, emptyBuffers, NoHost, trivial⟩, ⟨_, _, _, _, emptyBuffers, NoHost, _, _,
    emptyPrepared NoHost, [], Accept.empty_valid, by decide, Or.inr rfl⟩⟩

@[fva_witness r3] theorem r3_domain : fva_obligation% r3 :=
  ⟨⟨_, _, _, _, emptyBuffers, NoHost, trivial⟩, ⟨_, _, _, _, emptyBuffers, NoHost, _, _,
    emptyPrepared NoHost⟩⟩

end Subjects.Lz4C
