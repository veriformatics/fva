import Proofs.Lifted
import FVA.Spec.CAbi

/-! Explicit linking context for the two allocator calls of a 1 by 1 CPM invocation.
All defined functions come from the decoded artifact; only imports are supplied here.
No claim in this file asserts full R runtime or loader correctness. -/
namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- Allocator for exactly the two live allocations (4 and 8 bytes), disjoint and initially zero. -/
def allocator : Func :=
  { type := 1, locals := [], body :=
    [.localGet 1, .iconst .w32 4, .irelop .w32 .eq,
      .if_ (.val (.num .i32)) [.iconst .w32 131072] [.iconst .w32 131080]] }

/-- Free has no effect; neither block is subsequently reused in this invocation. -/
def deallocator : Func := { type := 3, locals := [], body := [] }

/-- Imported function types, in their artifact order. -/
noncomputable def importedTypes : List FuncType :=
  Lifted.module.imports.filterMap fun im => match im.desc with
    | .func k => Lifted.module.types[k]?
    | _ => none

/-- Imported functions: allocator/free are Wasm shims; all unused functions are hosts. -/
noncomputable def importsStore : Store :=
  { funcs := importedTypes.zipIdx.map fun (ft, k) =>
      if k = 12 then .wasm ft {} allocator
      else if k = 13 then .wasm ft {} deallocator
      else .host ft k,
    mems := [{ pages := 4, max := none, byte := fun _ => 0 }],
    tables := [{ type := ⟨⟨9, none⟩, .funcref⟩, elem := List.replicate 9 (.null .funcref) }],
    globals := (List.range 75).map fun k =>
      { type := ⟨if k = 1 ∨ k = 2 then .const else .var, .num .i32⟩,
        value := .i32 (if k = 0 then 65536 else 0) } }

/-- Import addresses have the same indexing as the original module. -/
noncomputable def importAddresses : List ExternVal :=
  (Lifted.module.imports.foldl (fun (acc : List ExternVal × Nat × Nat) im =>
    match im.desc with
    | .func _ => (acc.1 ++ [.func acc.2.1], acc.2.1 + 1, acc.2.2)
    | .global _ => (acc.1 ++ [.global acc.2.2], acc.2.1, acc.2.2 + 1)
    | .mem _ => (acc.1 ++ [.mem 0], acc.2.1, acc.2.2)
    | .table _ => (acc.1 ++ [.table 0], acc.2.1, acc.2.2)) ([], 0, 0)).1

/-- Allocate every defined function of the original module using FVA's allocator.
The relevant function uses no module globals/data/tables; this is an allocated calling context,
not a claim that instantiation, relocations and constructors were formally verified. -/
noncomputable def linked : Store × ModuleInst :=
  allocModule importsStore Lifted.module importAddresses
    (Lifted.module.globals.map fun _ => .i32 0) []

/-- Finite positive binary64 value 2^1023. -/
def huge : BitVec 64 := 0x7fe0000000000000

/-- Caller memory: structs, library value, and in-place output count. -/
def inputMemory (c L : BitVec 64) : MemInst :=
  let mem : MemInst := { pages := 4, max := none, byte := fun _ => 0 }
  let mem := mem.write 32776 4 1
  let mem := mem.write 32780 4 1
  let mem := mem.write 32792 4 1
  let mem := mem.write 32800 4 32832
  let mem := mem.write 32808 4 1
  let mem := mem.write 32812 4 1
  let mem := mem.write 32824 4 1
  let mem := mem.write 32832 8 L.toNat
  mem.write 32840 8 c.toNat

/-- A 1 by 1 matrix, a full double library-size matrix, and in-place count at 32840. -/
noncomputable def inputStore (c L : BitVec 64) : Store :=
  { linked.1 with mems := [inputMemory c L] }

end Proofs
