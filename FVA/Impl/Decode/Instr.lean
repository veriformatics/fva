import FVA.Impl.Decode.Reader

/-!
# Instruction decoding

Opcode dispatch is a tree of `Nat.blt` tests on spec §5.4's opcode ranges, then a short table
walk inside a family, so the kernel spends a handful of steps per opcode. `FVA.Proof.Decode`
proves the dispatch agrees with the spec tables (`FVA.Wasm.Binary.plainOps`, …).
-/

namespace FVA.Wasm.Decode

open FVA.Wasm

/-- The `k`-th entry of a table. -/
def nth {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, k + 1 => nth as k

/-- Value type of a type byte (spec §5.3.4); `v128` (`0x7B`) is outside the profile. -/
def valTypeOf (b : Nat) : Option ValType :=
  bif Nat.blt b 0x7C then
    (bif Nat.beq b 0x70 then some (.ref .funcref)
     else bif Nat.beq b 0x6F then some (.ref .externref) else none)
  else bif Nat.beq b 0x7F then some (.num .i32) else bif Nat.beq b 0x7E then some (.num .i64)
  else bif Nat.beq b 0x7D then some (.num .f32) else bif Nat.beq b 0x7C then some (.num .f64)
  else none

/-- A value type. -/
def valType (v n : Nat) : Res ValType :=
  (byte v n).bind fun b v' n' =>
  match valTypeOf b with
  | some t => .ok t v' n'
  | none => bif Nat.beq b 0x7B then .unsup n "v128 (SIMD)" else .bad n "malformed value type"

/-- A reference type. -/
def refType (v n : Nat) : Res RefType :=
  (byte v n).bind fun b v' n' =>
  bif Nat.beq b 0x70 then .ok .funcref v' n'
  else bif Nat.beq b 0x6F then .ok .externref v' n'
  else .bad n "malformed reference type"

/-- A block type: `0x40`, a value type, or a non-negative `s33` type index. -/
def blockType (v n : Nat) : Res BlockType :=
  (byte v n).bind fun b v' n' =>
  bif Nat.beq b 0x40 then .ok .empty v' n' else
  match valTypeOf b with
  | some t => .ok (.val t) v' n'
  | none =>
    bif Nat.beq b 0x7B then .unsup n "v128 (SIMD)" else
    (sleb 5 33 v n).bind fun x v n =>
    bif Nat.blt x (2 ^ 32) then .ok (.idx x) v n else .bad n "malformed block type"

/-- A `memarg`. -/
def memArg (v n : Nat) : Res MemArg :=
  (u32 v n).bind fun a v n => (u32 v n).bind fun o v n => .ok { align := a, offset := o } v n

/-- Integer comparison opcodes from `0x45`/`0x50`. -/
def intRelOps (w : Width) : List Instr :=
  [.itestEqz w, .irelop w .eq, .irelop w .ne, .irelop w (.lt .s), .irelop w (.lt .u),
   .irelop w (.gt .s), .irelop w (.gt .u), .irelop w (.le .s), .irelop w (.le .u),
   .irelop w (.ge .s), .irelop w (.ge .u)]

/-- Float comparison opcodes from `0x5B`/`0x61`. -/
def floatRelOps (w : Width) : List Instr :=
  [.frelop w .eq, .frelop w .ne, .frelop w .lt, .frelop w .gt, .frelop w .le, .frelop w .ge]

/-- Integer arithmetic opcodes from `0x67`/`0x79`. -/
def intArithOps (w : Width) : List Instr :=
  [.iunop w .clz, .iunop w .ctz, .iunop w .popcnt, .ibinop w .add, .ibinop w .sub,
   .ibinop w .mul, .ibinop w (.div .s), .ibinop w (.div .u), .ibinop w (.rem .s),
   .ibinop w (.rem .u), .ibinop w .and, .ibinop w .or, .ibinop w .xor, .ibinop w .shl,
   .ibinop w (.shr .s), .ibinop w (.shr .u), .ibinop w .rotl, .ibinop w .rotr]

/-- Float arithmetic opcodes from `0x8B`/`0x99`. -/
def floatArithOps (w : Width) : List Instr :=
  [.funop w .abs, .funop w .neg, .funop w .ceil, .funop w .floor, .funop w .trunc,
   .funop w .nearest, .funop w .sqrt, .fbinop w .add, .fbinop w .sub, .fbinop w .mul,
   .fbinop w .div, .fbinop w .min, .fbinop w .max, .fbinop w .copysign]

/-- Conversion opcodes `0xA7`–`0xBF`, then sign extension `0xC0`–`0xC4`. -/
def convOps : List Instr :=
  [.cvtop .wrap, .cvtop (.trunc .w32 .w32 .s), .cvtop (.trunc .w32 .w32 .u),
   .cvtop (.trunc .w32 .w64 .s), .cvtop (.trunc .w32 .w64 .u), .cvtop (.extend .s),
   .cvtop (.extend .u), .cvtop (.trunc .w64 .w32 .s), .cvtop (.trunc .w64 .w32 .u),
   .cvtop (.trunc .w64 .w64 .s), .cvtop (.trunc .w64 .w64 .u), .cvtop (.convert .w32 .w32 .s),
   .cvtop (.convert .w32 .w32 .u), .cvtop (.convert .w32 .w64 .s),
   .cvtop (.convert .w32 .w64 .u), .cvtop .demote, .cvtop (.convert .w64 .w32 .s),
   .cvtop (.convert .w64 .w32 .u), .cvtop (.convert .w64 .w64 .s),
   .cvtop (.convert .w64 .w64 .u), .cvtop .promote, .cvtop (.reinterpret .w32 true),
   .cvtop (.reinterpret .w64 true), .cvtop (.reinterpret .w32 false),
   .cvtop (.reinterpret .w64 false), .iunop .w32 .extend8s, .iunop .w32 .extend16s,
   .iunop .w64 .extend8s, .iunop .w64 .extend16s, .iunop .w64 .extend32s]

/-- Numeric opcodes `0x45`–`0xC4` (no immediates). -/
def numOp (op : Nat) : Option Instr :=
  bif Nat.blt op 0x67 then
    (bif Nat.blt op 0x5B then
      (bif Nat.blt op 0x50 then nth (intRelOps .w32) (op - 0x45)
       else nth (intRelOps .w64) (op - 0x50))
     else bif Nat.blt op 0x61 then nth (floatRelOps .w32) (op - 0x5B)
     else nth (floatRelOps .w64) (op - 0x61))
  else bif Nat.blt op 0x8B then
    (bif Nat.blt op 0x79 then nth (intArithOps .w32) (op - 0x67)
     else nth (intArithOps .w64) (op - 0x79))
  else bif Nat.blt op 0xA7 then
    (bif Nat.blt op 0x99 then nth (floatArithOps .w32) (op - 0x8B)
     else nth (floatArithOps .w64) (op - 0x99))
  else nth convOps (op - 0xA7)

/-- Load opcodes `0x28`–`0x35`. -/
def loadOps : List (MemArg → Instr) :=
  [.load .i32, .load .i64, .load .f32, .load .f64, .loadPacked .w32 .p8 .s,
   .loadPacked .w32 .p8 .u, .loadPacked .w32 .p16 .s, .loadPacked .w32 .p16 .u,
   .loadPacked .w64 .p8 .s, .loadPacked .w64 .p8 .u, .loadPacked .w64 .p16 .s,
   .loadPacked .w64 .p16 .u, .loadPacked .w64 .p32 .s, .loadPacked .w64 .p32 .u]

/-- Store opcodes `0x36`–`0x3E`. -/
def storeOps : List (MemArg → Instr) :=
  [.store .i32, .store .i64, .store .f32, .store .f64, .storePacked .w32 .p8,
   .storePacked .w32 .p16, .storePacked .w64 .p8, .storePacked .w64 .p16, .storePacked .w64 .p32]

/-- Index opcodes `0x20`–`0x26`. -/
def varOps : List (Nat → Instr) :=
  [.localGet, .localSet, .localTee, .globalGet, .globalSet, .tableGet, .tableSet]

/-- A `u32` immediate, then the instruction. -/
def withIdx (mk : Nat → Instr) (v n : Nat) : Res Instr :=
  (u32 v n).bind fun x v n => .ok (mk x) v n

/-- The zero byte standing for memory index 0. -/
def zeroByte (v n : Nat) : Res Unit :=
  (byte v n).bind fun b v' n' => bif Nat.beq b 0 then .ok () v' n' else .unsup n "multiple memories"

/-- `0xFC`-prefixed instructions (after the prefix byte). -/
def fcInstr (v n : Nat) : Res Instr :=
  (u32 v n).bind fun k v n =>
  bif Nat.blt k 8 then
    .ok (.cvtop (.truncSat (bif Nat.blt k 4 then .w32 else .w64)
      (bif Nat.blt (k % 4) 2 then .w32 else .w64) (bif Nat.beq (k % 2) 0 then .s else .u))) v n
  else bif Nat.beq k 8 then
    (u32 v n).bind fun x v n => (zeroByte v n).bind fun _ v n => .ok (.memoryInit x) v n
  else bif Nat.beq k 9 then withIdx .dataDrop v n
  else bif Nat.beq k 10 then
    (zeroByte v n).bind fun _ v n => (zeroByte v n).bind fun _ v n => .ok .memoryCopy v n
  else bif Nat.beq k 11 then (zeroByte v n).bind fun _ v n => .ok .memoryFill v n
  else bif Nat.beq k 12 then
    (u32 v n).bind fun y v n => (u32 v n).bind fun x v n => .ok (.tableInit x y) v n
  else bif Nat.beq k 13 then withIdx .elemDrop v n
  else bif Nat.beq k 14 then
    (u32 v n).bind fun x v n => (u32 v n).bind fun y v n => .ok (.tableCopy x y) v n
  else bif Nat.beq k 15 then withIdx .tableGrow v n
  else bif Nat.beq k 16 then withIdx .tableSize v n
  else bif Nat.beq k 17 then withIdx .tableFill v n
  else .bad n "illegal opcode"

/-- Opcodes below `0x20` other than structured control (`0x02`–`0x05`, `0x0B`). -/
def lowInstr (op v n r : Nat) : Res Instr :=
  bif Nat.blt op 0x0C then
    (bif Nat.beq op 0x00 then .ok .unreachable v n
     else bif Nat.beq op 0x01 then .ok .nop v n
     else .unsup r "exception handling")
  else bif Nat.blt op 0x10 then
    (bif Nat.beq op 0x0C then withIdx .br v n
     else bif Nat.beq op 0x0D then withIdx .brIf v n
     else bif Nat.beq op 0x0F then .ok .return_ v n
     else (vec u32 v n).bind fun ls v n => (u32 v n).bind fun l v n => .ok (.brTable ls l) v n)
  else bif Nat.beq op 0x10 then withIdx .call v n
  else bif Nat.beq op 0x11 then
    (u32 v n).bind fun y v n => (u32 v n).bind fun x v n => .ok (.callIndirect x y) v n
  else bif Nat.beq op 0x1A then .ok .drop v n
  else bif Nat.beq op 0x1B then .ok (.select none) v n
  else bif Nat.beq op 0x1C then (vec valType v n).bind fun ts v n => .ok (.select (some ts)) v n
  else bif Nat.blt op 0x14 then .unsup r "tail calls"
  else bif Nat.blt op 0x16 then .unsup r "typed function references"
  else bif Nat.beq op 0x18 || Nat.beq op 0x19 || Nat.beq op 0x1F then .unsup r "exception handling"
  else .bad r "illegal opcode"

/-- Opcodes from `0xC5`. -/
def highInstr (op v n r : Nat) : Res Instr :=
  bif Nat.beq op 0xD0 then (refType v n).bind fun t v n => .ok (.refNull t) v n
  else bif Nat.beq op 0xD1 then .ok .refIsNull v n
  else bif Nat.beq op 0xD2 then withIdx .refFunc v n
  else bif Nat.beq op 0xFC then fcInstr v n
  else bif Nat.blt op 0xD3 then .bad r "illegal opcode"
  else bif Nat.blt op 0xD7 then .unsup r "typed function references"
  else bif Nat.beq op 0xFB then .unsup r "GC (0xFB prefix)"
  else bif Nat.beq op 0xFD then .unsup r "SIMD (0xFD prefix)"
  else bif Nat.beq op 0xFE then .unsup r "threads/atomics (0xFE prefix)"
  else .bad r "illegal opcode"

/-- A non-structured instruction with opcode `op`; `(v, n)` follows the opcode, `r` = bytes
left at the opcode (for failures). Not recursive: `seq` handles block, loop and if. -/
def instr (op v n r : Nat) : Res Instr :=
  bif Nat.blt op 0x45 then
    (bif Nat.blt op 0x20 then lowInstr op v n r
     else bif Nat.blt op 0x28 then
       (match nth varOps (op - 0x20) with
        | some mk => withIdx mk v n
        | none => .bad r "illegal opcode")
     else bif Nat.blt op 0x3F then
       (match (bif Nat.blt op 0x36 then nth loadOps (op - 0x28) else nth storeOps (op - 0x36)) with
        | some mk => (memArg v n).bind fun m v n => .ok (mk m) v n
        | none => .bad r "illegal opcode")
     else bif Nat.beq op 0x3F then (zeroByte v n).bind fun _ v n => .ok .memorySize v n
     else bif Nat.beq op 0x40 then (zeroByte v n).bind fun _ v n => .ok .memoryGrow v n
     else bif Nat.beq op 0x41 then (sleb 5 32 v n).bind fun x v n => .ok (.iconst .w32 x) v n
     else bif Nat.beq op 0x42 then (sleb 10 64 v n).bind fun x v n => .ok (.iconst .w64 x) v n
     else bif Nat.beq op 0x43 then (leNat 4 v n).bind fun z v n => .ok (.fconst .w32 z) v n
     else (leNat 8 v n).bind fun z v n => .ok (.fconst .w64 z) v n)
  else bif Nat.blt op 0xC5 then
    (match numOp op with
     | some i => .ok i v n
     | none => .bad r "illegal opcode")
  else highInstr op v n r

/-- Instructions up to a terminator (`0x0B` end or `0x05` else), prepended in reverse to `acc`;
returns the terminator. Sequences iterate by tail calls and only nesting recurses, so kernel
evaluation depth follows block nesting. Structural on `fuel` (all recursion stays here);
callers pass the input length (each instruction takes ≥ 1 byte). -/
def seq : Nat → List Instr → Nat → Nat → Res (List Instr × Nat)
  | 0, _, _, n => .bad n "unexpected end"
  | fuel + 1, acc, v, n =>
    match n with
    | 0 => .bad 0 "unexpected end"
    | n' + 1 =>
      let op := Nat.land v 255
      let v' := Nat.shiftRight v 8
      let plain := (instr op v' n' n).bind fun i v n => seq fuel (i :: acc) v n
      bif Nat.blt 0x05 op then (bif Nat.beq op 0x0B then .ok (acc, op) v' n' else plain)
      else bif Nat.blt op 0x02 then plain
      else bif Nat.beq op 0x05 then .ok (acc, op) v' n'
      else (blockType v' n').bind fun bt v n =>
        (seq fuel [] v n).bind fun body v n =>
        bif Nat.beq op 0x04 then
          (bif Nat.beq body.2 0x0B then seq fuel (.if_ bt body.1.reverse [] :: acc) v n
           else (seq fuel [] v n).bind fun els v n =>
             bif Nat.beq els.2 0x0B then
               seq fuel (.if_ bt body.1.reverse els.1.reverse :: acc) v n
             else .bad n "else without if")
        else bif Nat.beq body.2 0x0B then
          seq fuel ((bif Nat.beq op 0x02 then Instr.block else Instr.loop) bt body.1.reverse :: acc)
            v n
        else .bad n "else without if"

/-- An expression: instructions terminated by `end`. -/
def expr (v n : Nat) : Res Expr :=
  (seq n [] v n).bind fun is v' n' =>
  bif Nat.beq is.2 0x0B then .ok is.1.reverse v' n' else .bad n "else without if"

end FVA.Wasm.Decode
