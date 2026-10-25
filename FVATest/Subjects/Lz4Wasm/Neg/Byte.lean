import FVATest.Subjects.Lz4Wasm.Proof
/-! E2: the output bytes are pinned to the real run. Changing any expected byte breaks the Holds
check; here the first byte is 0x30 (real: 0x31). -/
open FVA.Wasm.Exec Subjects.Lz4Wasm
example : Holds encFinal.store (inputAddr + 13)
    [0x30, 0x61, 0x62, 0x61, 0x01, 0x00, 0x50, 0x61, 0x61, 0x61, 0x62, 0x61] :=
  ⟨encFinalMem, encFinalMem_eq, by decide +kernel, by decide +kernel⟩
