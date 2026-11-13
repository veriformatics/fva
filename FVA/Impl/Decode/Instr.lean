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

/-- Number type of a type byte. -/
def numTypeOf (b : Nat) : Option NumType :=
  bif Nat.beq b 0x7F then some .i32 else bif Nat.beq b 0x7E then some .i64
  else bif Nat.beq b 0x7D then some .f32 else bif Nat.beq b 0x7C then some .f64 else none

/-- Abstract heap type of a byte inside P′ (`0x70` func, `0x6F` extern, `0x69` exn). -/
def absHeapOf (b : Nat) : Option AbsHeapType :=
  bif Nat.beq b 0x70 then some .func else bif Nat.beq b 0x6F then some .extern
  else bif Nat.beq b 0x69 then some .exn else none

/-- The class of an abstract heap type byte outside P′: `0x6A`–`0x6E` (array, struct, i31, eq,
any) and `0x71` (none) are GC types, `0x72`–`0x74` (noextern, nofunc, noexn) bottom types. -/
def absHeapExcluded (b : Nat) : Option FVA.Profile.Excluded :=
  bif (Nat.ble 0x6A b && Nat.ble b 0x6E) || Nat.beq b 0x71 then some .gcTypes
  else bif Nat.ble 0x72 b && Nat.ble b 0x74 then some .bottomTypes else none

/-- A heap type: an abstract type's byte, or a type index as a non-negative `s33`. -/
def heapType (v n : Nat) : Res HeapType :=
  match n with
  | 0 => .bad 0 "unexpected end"
  | n' + 1 =>
    let b := Nat.land v 255
    match absHeapOf b with
    | some a => .ok (.abs a) (Nat.shiftRight v 8) n'
    | none =>
      match absHeapExcluded b with
      | some c => excluded c (n' + 1) "heap type"
      | none =>
        (sleb 5 33 v (n' + 1)).bind fun x v n =>
        bif Nat.blt x (2 ^ 32) then .ok (.idx x) v n else .bad (n' + 1) "malformed heap type"

/-- A reference type: `0x63 ht` (nullable), `0x64 ht` (non-null), or an abstract heap type's
byte alone (nullable). -/
def refType (v n : Nat) : Res RefType :=
  (byte v n).bind fun b v' n' =>
  bif Nat.beq b 0x63 then (heapType v' n').bind fun ht v n => .ok ⟨true, ht⟩ v n
  else bif Nat.beq b 0x64 then (heapType v' n').bind fun ht v n => .ok ⟨false, ht⟩ v n
  else match absHeapOf b with
    | some a => .ok ⟨true, .abs a⟩ v' n'
    | none =>
      match absHeapExcluded b with
      | some c => excluded c n "reference type"
      | none => .bad n "malformed reference type"

/-- A value type: a number type's byte, `v128` (outside P′) or a reference type. -/
def valType (v n : Nat) : Res ValType :=
  match n with
  | 0 => .bad 0 "unexpected end"
  | n' + 1 =>
    let b := Nat.land v 255
    match numTypeOf b with
    | some t => .ok (.num t) (Nat.shiftRight v 8) n'
    | none =>
      bif Nat.beq b 0x7B then excluded .simd (n' + 1) "v128 value type"
      else bif Nat.beq b 0x63 || Nat.beq b 0x64 || (absHeapOf b).isSome ||
          (absHeapExcluded b).isSome then
        (refType v (n' + 1)).bind fun t v n => .ok (.ref t) v n
      else .bad (n' + 1) "malformed value type"

/-- Whether a byte starts a value type (or `v128`) rather than a block type's `s33` index: all
such bytes are one-byte negative `s33` values, so the two never overlap. -/
def valTypeStart (b : Nat) : Bool :=
  (numTypeOf b).isSome || Nat.beq b 0x7B || Nat.beq b 0x63 || Nat.beq b 0x64 ||
    (absHeapOf b).isSome || (absHeapExcluded b).isSome

/-- A block type: `0x40`, a value type, or a non-negative `s33` type index. -/
def blockType (v n : Nat) : Res BlockType :=
  match n with
  | 0 => .bad 0 "unexpected end"
  | n' + 1 =>
    let b := Nat.land v 255
    bif Nat.beq b 0x40 then .ok .empty (Nat.shiftRight v 8) n'
    else bif valTypeStart b then (valType v (n' + 1)).bind fun t v n => .ok (.val t) v n
    else
      (sleb 5 33 v (n' + 1)).bind fun x v n =>
      bif Nat.blt x (2 ^ 32) then .ok (.idx x) v n else .bad (n' + 1) "malformed block type"

/-- A memory index: 0 in P′, any LEB spelling. -/
def memIdx0 (v n : Nat) : Res Unit :=
  (u32 v n).bind fun x v' n' =>
  bif Nat.beq x 0 then .ok () v' n' else excluded .multiMemory n "memory index"

/-- A `memarg`: flags `n:u32` — the alignment below 2^6, or alignment `n − 2^6` and a memory
index below 2^7 — then the offset `u64`. -/
def memArg (v n : Nat) : Res MemArg :=
  (u32 v n).bind fun f v n =>
  bif Nat.blt f 64 then (u64 v n).bind fun o v n => .ok { align := f, offset := o } v n
  else bif Nat.blt f 128 then
    (memIdx0 v n).bind fun _ v n => (u64 v n).bind fun o v n =>
    .ok { align := f - 64, offset := o } v n
  else .bad n "malformed memop flags"

/-- A `try_table` handler clause. -/
def catchClause (v n : Nat) : Res Catch :=
  (byte v n).bind fun k v' n' =>
  bif Nat.beq k 0 then
    (u32 v' n').bind fun x v n => (u32 v n).bind fun l v n => .ok (.tag x l) v n
  else bif Nat.beq k 1 then
    (u32 v' n').bind fun x v n => (u32 v n).bind fun l v n => .ok (.tagRef x l) v n
  else bif Nat.beq k 2 then (u32 v' n').bind fun l v n => .ok (.all l) v n
  else bif Nat.beq k 3 then (u32 v' n').bind fun l v n => .ok (.allRef l) v n
  else .bad n "malformed catch clause"

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

/-- `0xFC`-prefixed instructions (after the prefix byte). -/
def fcInstr (v n : Nat) : Res Instr :=
  (u32 v n).bind fun k v n =>
  bif Nat.blt k 8 then
    .ok (.cvtop (.truncSat (bif Nat.blt k 4 then .w32 else .w64)
      (bif Nat.blt (k % 4) 2 then .w32 else .w64) (bif Nat.beq (k % 2) 0 then .s else .u))) v n
  else bif Nat.beq k 8 then
    (u32 v n).bind fun x v n => (memIdx0 v n).bind fun _ v n => .ok (.memoryInit x) v n
  else bif Nat.beq k 9 then withIdx .dataDrop v n
  else bif Nat.beq k 10 then
    (memIdx0 v n).bind fun _ v n => (memIdx0 v n).bind fun _ v n => .ok .memoryCopy v n
  else bif Nat.beq k 11 then (memIdx0 v n).bind fun _ v n => .ok .memoryFill v n
  else bif Nat.beq k 12 then
    (u32 v n).bind fun y v n => (u32 v n).bind fun x v n => .ok (.tableInit x y) v n
  else bif Nat.beq k 13 then withIdx .elemDrop v n
  else bif Nat.beq k 14 then
    (u32 v n).bind fun x v n => (u32 v n).bind fun y v n => .ok (.tableCopy x y) v n
  else bif Nat.beq k 15 then withIdx .tableGrow v n
  else bif Nat.beq k 16 then withIdx .tableSize v n
  else bif Nat.beq k 17 then withIdx .tableFill v n
  else .bad n "illegal opcode"

/-- Opcodes below `0x20` other than structured control (`0x02`–`0x05`, `0x0B`, `0x1F`). -/
def lowInstr (op v n r : Nat) : Res Instr :=
  bif Nat.blt op 0x0C then
    (bif Nat.beq op 0x00 then .ok .unreachable v n
     else bif Nat.beq op 0x01 then .ok .nop v n
     else bif Nat.beq op 0x08 then withIdx .throw v n
     else bif Nat.beq op 0x0A then .ok .throwRef v n
     else bif Nat.beq op 0x06 || Nat.beq op 0x07 || Nat.beq op 0x09 then
       excluded .legacyEh r "try, catch or rethrow"
     else .bad r "illegal opcode")
  else bif Nat.blt op 0x10 then
    (bif Nat.beq op 0x0C then withIdx .br v n
     else bif Nat.beq op 0x0D then withIdx .brIf v n
     else bif Nat.beq op 0x0F then .ok .return_ v n
     else (vec u32 v n).bind fun ls v n => (u32 v n).bind fun l v n => .ok (.brTable ls l) v n)
  else bif Nat.blt op 0x16 then
    (bif Nat.beq op 0x10 then withIdx .call v n
     else bif Nat.beq op 0x11 then
       (u32 v n).bind fun y v n => (u32 v n).bind fun x v n => .ok (.callIndirect x y) v n
     else bif Nat.beq op 0x12 then withIdx .returnCall v n
     else bif Nat.beq op 0x13 then
       (u32 v n).bind fun y v n => (u32 v n).bind fun x v n =>
       .ok (.returnCallIndirect x y) v n
     else bif Nat.beq op 0x14 then withIdx .callRef v n
     else withIdx .returnCallRef v n)
  else bif Nat.beq op 0x1A then .ok .drop v n
  else bif Nat.beq op 0x1B then .ok (.select none) v n
  else bif Nat.beq op 0x1C then (vec valType v n).bind fun ts v n => .ok (.select (some ts)) v n
  else bif Nat.beq op 0x18 || Nat.beq op 0x19 then excluded .legacyEh r "delegate or catch_all"
  else .bad r "illegal opcode"

/-- Opcodes from `0xC5`. -/
def highInstr (op v n r : Nat) : Res Instr :=
  bif Nat.beq op 0xD0 then (heapType v n).bind fun ht v n => .ok (.refNull ht) v n
  else bif Nat.beq op 0xD1 then .ok .refIsNull v n
  else bif Nat.beq op 0xD2 then withIdx .refFunc v n
  else bif Nat.beq op 0xD4 then .ok .refAsNonNull v n
  else bif Nat.beq op 0xD5 then withIdx .brOnNull v n
  else bif Nat.beq op 0xD6 then withIdx .brOnNonNull v n
  else bif Nat.beq op 0xFC then fcInstr v n
  else bif Nat.beq op 0xD3 then excluded .gcInstrs r "ref.eq"
  else bif Nat.beq op 0xFB then excluded .gcInstrs r "0xFB prefix"
  else bif Nat.beq op 0xFD then excluded .simd r "0xFD prefix"
  else bif Nat.beq op 0xFE then excluded .threads r "0xFE prefix"
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
     else bif Nat.beq op 0x3F then (memIdx0 v n).bind fun _ v n => .ok .memorySize v n
     else bif Nat.beq op 0x40 then (memIdx0 v n).bind fun _ v n => .ok .memoryGrow v n
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
returns the terminator. Sequences iterate by tail calls and only nesting recurses (`block`,
`loop`, `if`, `try_table`), so kernel evaluation depth follows block nesting. Structural on
`fuel` (all recursion stays here); callers pass the input length (each instruction takes ≥ 1
byte). -/
def seq : Nat → List Instr → Nat → Nat → Res (List Instr × Nat)
  | 0, _, _, n => .bad n "unexpected end"
  | fuel + 1, acc, v, n =>
    match n with
    | 0 => .bad 0 "unexpected end"
    | n' + 1 =>
      let op := Nat.land v 255
      let v' := Nat.shiftRight v 8
      let plain := (instr op v' n' n).bind fun i v n => seq fuel (i :: acc) v n
      bif Nat.blt 0x05 op then
        (bif Nat.beq op 0x0B then .ok (acc, op) v' n'
         else bif Nat.beq op 0x1F then
           (blockType v' n').bind fun bt v n => (vec catchClause v n).bind fun cs v n =>
           (seq fuel [] v n).bind fun body v n =>
           bif Nat.beq body.2 0x0B then seq fuel (.tryTable bt cs body.1.reverse :: acc) v n
           else .bad n "else without if"
         else plain)
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
