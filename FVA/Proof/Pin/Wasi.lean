import FVA.Proof.Wasi.Examples

/-!
# WASI model behavior, pinned

Concrete cases of behavior the U29a contract specifies that a cheap proof must fix: a model
mutant only the `test:wasi` vectors distinguish can exhaust the vector run's memory or time before
any vector fails (fvamut: `inconclusive … crash: memory over` | `inconclusive test:wasi timeout`;
the runner reads every vector), while a kernel `decide` here fails it at the `proofs` stage.
Expected values come from a source, never from running `exec` (`FVA/Proof/Wasi/Examples.lean`'s
world and helpers).
-/

namespace FVA.Wasi.Pin

open FVA.Wasi FVA.Wasi.Examples

/-- `fd_write` moves `iovs_len` buffers, never as many as the result pointer's value (Wf
fd_write: `$iovs` = a `ciovec_array` = pointer + length parameters, the `$size` result written
through the last parameter): with the count cell at address 0, the one buffer reaches stdout. -/
theorem fdWrite_iovsLen :
    let r := call σ₀ [(64, b "AB"), (16, iov [(64, 2)])] .fdWrite [1, 16, 1, 0]
    r.1.stdout = b "AB" ∧ r.2.1 = some 0 ∧ r.2.2.read 0 4 = 2 := by
  decide

/-- `fd_read` fills `iovs_len` buffers (Wf fd_read: `$iovs` = an `iovec_array`): with the count
cell at address 0, stdin's `in` lands in the one buffer. -/
theorem fdRead_iovsLen :
    let r := call σ₀ [(16, iov [(64, 2)])] .fdRead [0, 16, 1, 0]
    r.2.1 = some 0 ∧ r.2.2.read 0 4 = 2 ∧ r.2.2.byte 64 = 105 ∧ r.2.2.byte 65 = 110 := by
  decide

/-- `fd_write`'s buffer regions = its `iovs_len` iovecs (Wf fd_write: `$iovs` = a
`ciovec_array`), never as many as the result pointer's value: with the count cell at address 0, a
buffer crossing the memory end lies outside the profile (wasmtime traps at the pointer: WD
Pointers, p1:184-204, p1:706-723; `inProfile`), one ending at the last byte inside. -/
theorem fdWrite_bufferEnd :
    ok σ₀ [(16, iov [(65535, 2)])] .fdWrite [1, 16, 1, 0] = false ∧
      ok σ₀ [(16, iov [(65534, 2)])] .fdWrite [1, 16, 1, 0] = true := by
  decide

end FVA.Wasi.Pin
