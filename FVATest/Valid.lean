import FVA.Impl.Valid

namespace FVA.Test.Valid

open FVA.Wasm FVA.Wasm.Valid

/-- A function fixture keeps its local runs compressed. -/
def one (body : Expr) (params results : List ValType := [])
    (locals : List (Nat × ValType) := []) : Module :=
  { types := [[⟨params, results⟩]], funcs := [⟨0, locals, body⟩] }

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
  types := [[⟨[], []⟩], [⟨[.num .i32], []⟩]]
  funcs := [⟨0, [], [.iconst .w32 0, .loop (.idx 1) [.br 0]]⟩] }
#guard !validate {
  types := [[⟨[], []⟩], [⟨[.num .i32], []⟩]]
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
-- 3.0 constants (R1): a global reads the imported and the earlier defined immutable globals;
-- a table initializer the imported ones alone; segments every immutable global
#guard validate { globals := [⟨⟨.const, .num .i32⟩, [.iconst .w32 0]⟩,
  ⟨⟨.const, .num .i32⟩, [.globalGet 0]⟩] }
#guard !validate { globals := [⟨⟨.const, .num .i32⟩, [.globalGet 0]⟩] }
#guard !validate { globals := [⟨⟨.const, .num .i32⟩, [.globalGet 1]⟩,
  ⟨⟨.const, .num .i32⟩, [.iconst .w32 0]⟩] }
#guard !validate { globals := [⟨⟨.var, .num .i32⟩, [.iconst .w32 0]⟩,
  ⟨⟨.const, .num .i32⟩, [.globalGet 0]⟩] }
#guard !validate { one [] with
  globals := [⟨⟨.const, .ref .funcref⟩, [.refFunc 0]⟩]
  tables := [⟨⟨⟨1, none⟩, .funcref⟩, [.globalGet 0]⟩] }
#guard validate { one [] with
  globals := [⟨⟨.const, .num .i32⟩, [.iconst .w32 0]⟩]
  tables := [⟨⟨⟨1, none⟩, .funcref⟩, [.refNull (.abs .func)]⟩]
  elems := [⟨.funcref, [[.refNull (.abs .func)]], .active 0 [.globalGet 0]⟩] }
#guard validate { imports := [⟨"m", "memory", .mem ⟨0, none⟩⟩] }
#guard !validate { imports := [⟨"m", "memory", .mem ⟨0, none⟩⟩], mems := [⟨0, none⟩] }
#guard !validate { mems := [⟨0, none⟩, ⟨0, none⟩] }
#guard !validate { mems := [⟨2 ^ 16 + 1, none⟩] }
#guard !validate { tables := [⟨⟨⟨2 ^ 32, none⟩, .funcref⟩, [.refNull (.abs .func)]⟩] }
#guard !validate { tables := [⟨⟨⟨2, some 1⟩, .funcref⟩, [.refNull (.abs .func)]⟩] }
#guard validate { tables := [⟨⟨⟨1, none⟩, .funcref⟩, [.refNull (.abs .func)]⟩] }

-- P′ (U28c): recursive groups, tags, typed references, non-defaultable locals, table
-- initializers; element segments typed at their declared type
#guard validate { types := [[⟨[], []⟩, ⟨[], []⟩]] }
#guard validate { types := [[⟨[], []⟩]], tags := [⟨0⟩] }
#guard !validate { types := [[⟨[], [.num .i32]⟩]], tags := [⟨0⟩] }
#guard validate {
  types := [[⟨[], []⟩]]
  imports := [⟨"m", "t", .tag 0⟩]
  exports := [⟨"t", .tag 0⟩] }
#guard !validate { exports := [⟨"t", .tag 0⟩] }
#guard validate (one [.refNull (.abs .exn)] [] [.ref .exnref])
#guard validate (one [] [] [] [(1, .ref ⟨false, .abs .func⟩)])
#guard validate (one [.refNull (.idx 0), .drop])
#guard validate { one [] with
  tables := [⟨⟨⟨1, none⟩, ⟨false, .abs .func⟩⟩, [.refFunc 0]⟩] }
#guard validate { one [] with elems := [⟨⟨false, .abs .func⟩, [[.refFunc 0]], .declarative⟩] }
#guard !validate { one [] with
  elems := [⟨⟨false, .abs .func⟩, [[.refNull (.abs .func)]], .declarative⟩] }
-- raw source annotations: closed forms are never source; indices name existing types, inside
-- unreachable code too; a group names earlier types or its own members
#guard !validate (one [.refNull (.rec_ 0), .drop])
#guard !validate (one [.refNull (.def_ ⟨[⟨[], []⟩], 0⟩), .drop])
#guard !validate (one [.unreachable, .refNull (.idx 5), .drop])
#guard !validate (one [.unreachable, .block (.idx 5) []])
#guard validate { types := [[⟨[.ref ⟨true, .idx 0⟩], []⟩]] }
#guard !validate { types := [[⟨[.ref ⟨true, .idx 1⟩], []⟩]] }
#guard !validate { types := [[⟨[.ref ⟨true, .rec_ 0⟩], []⟩]] }
-- initialization: a non-defaultable local reads only after a write in its block or before;
-- unreachable code initializes nothing; a block's writes end with it; a 2^32 − 1 run stays one
#guard validate (one [.refNull (.abs .func), .refAsNonNull, .localSet 0, .localGet 0, .drop]
  [] [] [(1, .ref ⟨false, .abs .func⟩)])
#guard !validate (one [.localGet 0, .drop] [] [] [(1, .ref ⟨false, .abs .func⟩)])
#guard !validate (one [.unreachable, .localGet 0, .drop] [] [] [(1, .ref ⟨false, .abs .func⟩)])
#guard !validate (one [.block .empty [.refNull (.abs .func), .refAsNonNull, .localSet 0],
  .localGet 0, .drop] [] [] [(1, .ref ⟨false, .abs .func⟩)])
#guard validate (one [.refNull (.abs .func), .refAsNonNull, .localSet 0,
  .block .empty [.localGet 0, .drop]] [] [] [(1, .ref ⟨false, .abs .func⟩)])
#guard validate (one [.refNull (.abs .func), .refAsNonNull, .localSet (2 ^ 32 - 2),
  .localGet (2 ^ 32 - 2), .drop] [] [] [(2 ^ 32 - 1, .ref ⟨false, .abs .func⟩)])
#guard !validate
  (one [.localGet (2 ^ 32 - 2), .drop] [] [] [(2 ^ 32 - 1, .ref ⟨false, .abs .func⟩)])
-- contract X10: a zero-count run still names a valid type (wasm-tools rejects it too; SpecTec 5.4
-- `Blocals` erases the run before `Func_ok`)
#guard !validate (one [] [] [] [(0, .ref ⟨true, .idx 1⟩)])
#guard validate (one [] [] [] [(0, .ref ⟨true, .idx 0⟩)])
#guard !Check.expr { locals := [(1, ⟨false, .ref ⟨false, .abs .func⟩⟩)] } [.localGet 0, .drop] []
#guard Check.expr { locals := [(1, ⟨false, .ref ⟨false, .abs .func⟩⟩)], sets := [0] }
  [.localGet 0, .drop] []
-- operand bottoms: the bottom reference matches references alone; `br_table` keeps it
#guard !Check.matchType .refBot (.val (.num .i32))
#guard Check.matchType .refBot (.val (.ref .funcref))
#guard Check.matchType .bot .refBot
#guard !Check.matchType (.val (.ref .funcref)) .refBot
#guard Check.expr { labels := [[.ref ⟨false, .def_ ⟨[⟨[], []⟩], 0⟩⟩],
    [.ref ⟨false, .def_ ⟨[⟨[.num .i32], []⟩], 0⟩⟩]] }
  [.unreachable, .refAsNonNull, .iconst .w32 0, .brTable [0] 1] []
#guard !Check.expr { labels := [[.ref ⟨false, .def_ ⟨[⟨[], []⟩], 0⟩⟩],
    [.ref ⟨false, .def_ ⟨[⟨[.num .i32], []⟩], 0⟩⟩]] }
  [.unreachable, .refAsNonNull, .brTable [0] 1] []
-- typed calls pop the reference first, then the parameters
#guard validate {
  types := [[⟨[.num .i32], []⟩]]
  funcs := [⟨0, [], [.localGet 0, .refNull (.idx 0), .callRef 0]⟩] }
#guard !validate {
  types := [[⟨[.num .i32], []⟩]]
  funcs := [⟨0, [], [.refNull (.idx 0), .localGet 0, .callRef 0]⟩] }

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
#guard validate (one [] [] [] [(2 ^ 32, .num .i32)])
#guard validate (one [.localGet 0, .drop] [.num .i64] [] [(0, .num .i32)])
#guard !validate { one [] with exports := [⟨"f", .func 0⟩, ⟨"f", .func 0⟩] }
#guard !validate { one [.iconst .w32 0] [] [.num .i32] with start := some 0 }
#guard validate { one [] with start := some 0 }

end FVA.Test.Valid
