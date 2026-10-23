import FVA.Impl.Valid

namespace FVA.Test.Valid

open FVA.Wasm FVA.Wasm.Valid

/-- A function fixture keeps its local runs compressed. -/
def one (body : Expr) (params results : List ValType := [])
    (locals : List (Nat × ValType) := []) : Module :=
  { types := [⟨params, results⟩], funcs := [⟨0, locals, body⟩] }

#guard validate {}
#guard validate (one [.iconst .w32 7] [] [.num .i32])
#guard !validate (one [.iconst .w32 7])
#guard !validate (one [.ibinop .w32 .add] [.num .i32] [.num .i32])
#guard validate (one [.unreachable, .ibinop .w32 .add] [] [.num .i32])
#guard !validate (one [.unreachable, .iconst .w64 0, .ibinop .w32 .add] [] [.num .i32])
#guard !validate (one [.unreachable, .iconst .w32 0])

-- The selector is a real i32 operand; bottom label arguments may match different types.
#guard Check.expr { labels := [[.num .i32], [.num .i64]] }
  [.unreachable, .brTable [0] 1] []
#guard !Check.expr { labels := [[.num .i32], [.num .i64]] }
  [.unreachable, .iconst .w32 0, .iconst .w32 0, .brTable [0] 1] []
#guard !Check.expr { labels := [[]] } [.brTable [] 0] []
#guard Check.expr { labels := [[]] } [.iconst .w32 0, .brTable [] 0] []
#guard validate (one [.br 0])
#guard !validate (one [.br 1])
#guard !validate (one [.unreachable, .br 1])
#guard !Check.expr {} [.return_] []
#guard validate (one [.return_])
#guard validate (one [.block (.val (.ref .funcref)) [.unreachable, .select none]]
  [] [.ref .funcref])

-- A loop branches with its parameters, not its results.
#guard validate (one [.loop (.val (.num .i32)) [.br 0]] [] [.num .i32])
#guard !validate (one [.loop (.val (.num .i32)) []] [] [.num .i32])
#guard validate {
  types := [⟨[], []⟩, ⟨[.num .i32], []⟩]
  funcs := [⟨0, [], [.iconst .w32 0, .loop (.idx 1) [.br 0]]⟩] }
#guard !validate {
  types := [⟨[], []⟩, ⟨[.num .i32], []⟩]
  funcs := [⟨0, [], [.iconst .w32 0, .loop (.idx 1) [.drop, .br 0]]⟩] }

#guard !validate (one [.refFunc 0, .drop])
#guard validate { one [.refFunc 0, .drop] with exports := [⟨"f", .func 0⟩] }
#guard validate { one [.refFunc 0, .drop] with
  elems := [⟨.funcref, [[.refFunc 0]], .declarative⟩] }
#guard !validate { one [.refFunc 1, .drop] with exports := [⟨"f", .func 0⟩] }

#guard validate {
  imports := [⟨"m", "g", .global ⟨.const, .num .i32⟩⟩]
  globals := [⟨⟨.const, .num .i32⟩, [.globalGet 0]⟩] }
#guard !validate {
  imports := [⟨"m", "g", .global ⟨.var, .num .i32⟩⟩]
  globals := [⟨⟨.const, .num .i32⟩, [.globalGet 0]⟩] }
#guard !validate { globals := [⟨⟨.const, .num .i32⟩, [.iconst .w32 0]⟩,
  ⟨⟨.const, .num .i32⟩, [.globalGet 0]⟩] }
#guard validate { imports := [⟨"m", "memory", .mem ⟨0, none⟩⟩] }
#guard !validate { imports := [⟨"m", "memory", .mem ⟨0, none⟩⟩], mems := [⟨0, none⟩] }
#guard !validate { mems := [⟨0, none⟩, ⟨0, none⟩] }
#guard !validate { mems := [⟨2 ^ 16 + 1, none⟩] }
#guard !validate { tables := [⟨⟨2 ^ 32, none⟩, .funcref⟩] }
#guard !validate { tables := [⟨⟨2, some 1⟩, .funcref⟩] }

#guard !validate (one [.iconst .w32 (2 ^ 32)] [] [.num .i32])
#guard !validate (one [.fconst .w64 (2 ^ 64)] [] [.num .f64])
#guard !validate (one [.unreachable, .iunop .w32 .extend32s] [] [.num .i32])
#guard !validate { one [.iconst .w32 0, .loadPacked .w32 .p32 .u ⟨0, 0⟩] [] [.num .i32]
  with mems := [⟨0, none⟩] }
#guard !validate { one [.iconst .w32 0, .load .i32 ⟨2 ^ 32, 0⟩] [] [.num .i32]
  with mems := [⟨0, none⟩] }
#guard !validate { one [.iconst .w32 0, .load .i32 ⟨0, 2 ^ 32⟩] [] [.num .i32]
  with mems := [⟨0, none⟩] }

#guard validate (one [.localGet (2 ^ 32 - 2), .drop] [] [] [(2 ^ 32 - 1, .num .i32)])
#guard !validate (one [.localGet (2 ^ 32 - 1), .drop] [] [] [(2 ^ 32 - 1, .num .i32)])
#guard !validate (one [] [] [] [(2 ^ 32, .num .i32)])
#guard validate (one [.localGet 0, .drop] [.num .i64] [] [(0, .num .i32)])
#guard !validate { one [] with exports := [⟨"f", .func 0⟩, ⟨"f", .func 0⟩] }
#guard !validate { one [.iconst .w32 0] [] [.num .i32] with start := some 0 }
#guard validate { one [] with start := some 0 }

end FVA.Test.Valid
