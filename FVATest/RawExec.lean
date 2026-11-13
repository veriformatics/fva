import FVA.Impl.Exec.Ref

/-!
# Raw-state stepper fixtures (U28b E4)

Configurations no valid script reaches, checked at build time (`lake --wfail test`): an unset
non-defaultable local has no value to read (3.0 `$local` is undefined there: the stepper is stuck,
it never invents a null); a lookup that fails — a tag index or address, an exception address, a
function index or address, a type index — never manufactures an entity. Controls: the same
configurations with the entity present step as the rules say.
-/

namespace FVA.Test.RawExec

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

/-- The instructions after one step, if it steps. -/
def next (c : Config) : Option (List AInstr) := (step c).map (·.instrs)

/-- The final instructions of a run of at most `n` steps. -/
def final (n : Nat) (c : Config) : Option (List AInstr) := (Ref.run n c).map (·.instrs)

/-- An instance naming tag address `ta` at index 0 and function address `fa` at index 0. -/
def inst (ta fa : List Nat) : ModuleInst := { tags := ta, funcs := fa }

/-- `[] → []`. -/
def unitT : DefType := ⟨[⟨[], []⟩], 0⟩

/-- A store with tag 0 of type `[] → []` and function 0 (body `nop`). -/
def store : Store :=
  { tags := [⟨unitT⟩], funcs := [.wasm unitT (inst [0] [0]) ⟨0, [], [.nop]⟩],
    exns := [⟨0, []⟩] }

-- an unset local: no read (stuck), a set one reads its value; `local.set` writes `some v`
#guard (next ⟨{}, ⟨[none], {}⟩, [.plain (.localGet 0)]⟩).isNone
#guard match next ⟨{}, ⟨[some (.i32 7)], {}⟩, [.plain (.localGet 0)]⟩ with
  | some [.plain (.iconst .w32 7)] => true
  | _ => false
#guard match final 10 ⟨{}, ⟨[none], {}⟩,
    [(Val.i32 5).instr, .plain (.localSet 0), .plain (.localGet 0)]⟩ with
  | some [.plain (.iconst .w32 5)] => true
  | _ => false

-- `throw x`: a tag index the instance lacks, or a tag address the store lacks, is stuck
#guard (next ⟨store, ⟨[], inst [] []⟩, [.plain (.throw 0)]⟩).isNone
#guard (next ⟨store, ⟨[], inst [3] []⟩, [.plain (.throw 0)]⟩).isNone
#guard match next ⟨store, ⟨[], inst [0] []⟩, [.plain (.throw 0)]⟩ with
  | some [.refExnAddr 1, .plain .throwRef] => true
  | _ => false

-- a tag whose type has results (no valid module has one): `throw` has no rule (SpecTec 4.3
-- `Step/throw` expands the tag type to `FUNC t^n -> eps`; the interpreter asserts `ts2 = []`)
#guard (next ⟨{ tags := [⟨⟨[⟨[], [.num .i32]⟩], 0⟩⟩] }, ⟨[], inst [0] []⟩,
  [.plain (.throw 0)]⟩).isNone

-- a tagged clause whose tag index or exception lookup fails does not match: the next clause
#guard match next ⟨store, ⟨[], inst [] []⟩, [.handler 0 [.tag 0 0] (throwing 0)]⟩ with
  | some [.handler 0 [] [.refExnAddr 0, .plain .throwRef]] => true
  | _ => false
#guard match next ⟨store, ⟨[], inst [0] []⟩, [.handler 0 [.tagRef 0 0] (throwing 4)]⟩ with
  | some [.handler 0 [] [.refExnAddr 4, .plain .throwRef]] => true
  | _ => false
#guard match next ⟨store, ⟨[], inst [0] []⟩, [.handler 0 [.tag 0 0] (throwing 0)]⟩ with
  | some [.plain (.br 0)] => true
  | _ => false

-- a missing function index or address: no call
#guard (next ⟨store, ⟨[], inst [] []⟩, [.plain (.returnCall 0)]⟩).isNone
#guard (next ⟨store, ⟨[], inst [] []⟩, [.returnInvoke 3]⟩).isNone
#guard (next ⟨store, ⟨[], inst [] []⟩, [.invoke 3]⟩).isNone
#guard match next ⟨store, ⟨[], inst [] [0]⟩, [.plain (.returnCall 0)]⟩ with
  | some [.returnInvoke 0] => true
  | _ => false

-- a block type index the instance lacks: no block
#guard (next ⟨store, ⟨[], inst [] []⟩, [.plain (.block (.idx 0) [])]⟩).isNone
#guard match next ⟨store, ⟨[], { types := [unitT] }⟩, [.plain (.block (.idx 0) [])]⟩ with
  | some [.label 0 [] []] => true
  | _ => false

end FVA.Test.RawExec
