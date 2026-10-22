import FVA.Impl.Decode.Reader

/-!
# Instruction decoding

Opcode dispatch uses arithmetic on ranges (spec §5.4 groups opcodes by family), so the kernel
compares a handful of numerals per instruction instead of scanning a 200-entry table.
`FVA.Proof.Decode` proves the dispatch agrees with the spec tables.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm

/-- Value types (spec §5.3.4); `v128` (`0x7B`) is outside the profile. -/
def valTypeOf (b : Nat) : Option ValType :=
  if b = 0x7F then some (.num .i32) else if b = 0x7E then some (.num .i64)
  else if b = 0x7D then some (.num .f32) else if b = 0x7C then some (.num .f64)
  else if b = 0x70 then some (.ref .funcref) else if b = 0x6F then some (.ref .externref)
  else none

/-- Read a value type. -/
def valType (r : Reader) : Res ValType := do
  let (b, r') ← r.byte
  match valTypeOf b.toNat with
  | some t => .ok (t, r')
  | none => if b.toNat = 0x7B then r.unsup "v128 (SIMD)" else r.bad "malformed value type"

/-- Read a reference type. -/
def refType (r : Reader) : Res RefType := do
  let (b, r') ← r.byte
  if b.toNat = 0x70 then .ok (.funcref, r')
  else if b.toNat = 0x6F then .ok (.externref, r')
  else r.bad "malformed reference type"

/-- Read a block type: `0x40`, a value type, or a non-negative `s33` index. -/
def blockType (r : Reader) : Res BlockType := do
  let (b, r') ← r.byte
  if b.toNat = 0x40 then .ok (.empty, r')
  else match valTypeOf b.toNat with
    | some t => .ok (.val t, r')
    | none =>
      if b.toNat = 0x7B then r.unsup "v128 (SIMD)"
      else do
        let (x, r') ← sleb 5 33 r
        if 0 ≤ x then .ok (.idx x.toNat, r') else r.bad "malformed block type"

/-- Read a `memarg`. -/
def memArg (r : Reader) : Res MemArg := do
  let (a, r) ← u32 r
  let (o, r) ← u32 r
  .ok ({ align := a, offset := o }, r)

/-- Integer comparison and test opcodes `0x45`–`0x5A`, index `k` within a width group. -/
def intRelOp (w : Width) : Nat → Option Instr
  | 0 => some (.itestEqz w) | 1 => some (.irelop w .eq) | 2 => some (.irelop w .ne)
  | 3 => some (.irelop w (.lt .s)) | 4 => some (.irelop w (.lt .u))
  | 5 => some (.irelop w (.gt .s)) | 6 => some (.irelop w (.gt .u))
  | 7 => some (.irelop w (.le .s)) | 8 => some (.irelop w (.le .u))
  | 9 => some (.irelop w (.ge .s)) | 10 => some (.irelop w (.ge .u))
  | _ => none

/-- Float comparison opcodes `0x5B`–`0x66`. -/
def floatRelOp (w : Width) : Nat → Option Instr
  | 0 => some (.frelop w .eq) | 1 => some (.frelop w .ne) | 2 => some (.frelop w .lt)
  | 3 => some (.frelop w .gt) | 4 => some (.frelop w .le) | 5 => some (.frelop w .ge)
  | _ => none

/-- Integer arithmetic opcodes `0x67`–`0x8A`. -/
def intArithOp (w : Width) : Nat → Option Instr
  | 0 => some (.iunop w .clz) | 1 => some (.iunop w .ctz) | 2 => some (.iunop w .popcnt)
  | 3 => some (.ibinop w .add) | 4 => some (.ibinop w .sub) | 5 => some (.ibinop w .mul)
  | 6 => some (.ibinop w (.div .s)) | 7 => some (.ibinop w (.div .u))
  | 8 => some (.ibinop w (.rem .s)) | 9 => some (.ibinop w (.rem .u))
  | 10 => some (.ibinop w .and) | 11 => some (.ibinop w .or) | 12 => some (.ibinop w .xor)
  | 13 => some (.ibinop w .shl) | 14 => some (.ibinop w (.shr .s))
  | 15 => some (.ibinop w (.shr .u)) | 16 => some (.ibinop w .rotl)
  | 17 => some (.ibinop w .rotr)
  | _ => none

/-- Float arithmetic opcodes `0x8B`–`0xA6`. -/
def floatArithOp (w : Width) : Nat → Option Instr
  | 0 => some (.funop w .abs) | 1 => some (.funop w .neg) | 2 => some (.funop w .ceil)
  | 3 => some (.funop w .floor) | 4 => some (.funop w .trunc) | 5 => some (.funop w .nearest)
  | 6 => some (.funop w .sqrt) | 7 => some (.fbinop w .add) | 8 => some (.fbinop w .sub)
  | 9 => some (.fbinop w .mul) | 10 => some (.fbinop w .div) | 11 => some (.fbinop w .min)
  | 12 => some (.fbinop w .max) | 13 => some (.fbinop w .copysign)
  | _ => none

/-- Conversion opcodes `0xA7`–`0xBF` (index from `0xA7`). -/
def convOp : Nat → Option Instr
  | 0 => some (.cvtop .wrap)
  | 1 => some (.cvtop (.trunc .w32 .w32 .s)) | 2 => some (.cvtop (.trunc .w32 .w32 .u))
  | 3 => some (.cvtop (.trunc .w32 .w64 .s)) | 4 => some (.cvtop (.trunc .w32 .w64 .u))
  | 5 => some (.cvtop (.extend .s)) | 6 => some (.cvtop (.extend .u))
  | 7 => some (.cvtop (.trunc .w64 .w32 .s)) | 8 => some (.cvtop (.trunc .w64 .w32 .u))
  | 9 => some (.cvtop (.trunc .w64 .w64 .s)) | 10 => some (.cvtop (.trunc .w64 .w64 .u))
  | 11 => some (.cvtop (.convert .w32 .w32 .s)) | 12 => some (.cvtop (.convert .w32 .w32 .u))
  | 13 => some (.cvtop (.convert .w32 .w64 .s)) | 14 => some (.cvtop (.convert .w32 .w64 .u))
  | 15 => some (.cvtop .demote)
  | 16 => some (.cvtop (.convert .w64 .w32 .s)) | 17 => some (.cvtop (.convert .w64 .w32 .u))
  | 18 => some (.cvtop (.convert .w64 .w64 .s)) | 19 => some (.cvtop (.convert .w64 .w64 .u))
  | 20 => some (.cvtop .promote)
  | 21 => some (.cvtop (.reinterpret .w32 true)) | 22 => some (.cvtop (.reinterpret .w64 true))
  | 23 => some (.cvtop (.reinterpret .w32 false)) | 24 => some (.cvtop (.reinterpret .w64 false))
  | _ => none

/-- One-byte opcodes without immediates (the spec table `FVA.Wasm.Binary.plainOps`). -/
def plainOpOf (op : Nat) : Option Instr :=
  if op < 0x45 then
    if op = 0x00 then some .unreachable else if op = 0x01 then some .nop
    else if op = 0x0F then some .return_ else if op = 0x1A then some .drop
    else if op = 0x1B then some (.select none) else none
  else if op < 0x50 then intRelOp .w32 (op - 0x45)
  else if op < 0x5B then intRelOp .w64 (op - 0x50)
  else if op < 0x61 then floatRelOp .w32 (op - 0x5B)
  else if op < 0x67 then floatRelOp .w64 (op - 0x61)
  else if op < 0x79 then intArithOp .w32 (op - 0x67)
  else if op < 0x8B then intArithOp .w64 (op - 0x79)
  else if op < 0x99 then floatArithOp .w32 (op - 0x8B)
  else if op < 0xA7 then floatArithOp .w64 (op - 0x99)
  else if op < 0xC0 then convOp (op - 0xA7)
  else if op = 0xC0 then some (.iunop .w32 .extend8s)
  else if op = 0xC1 then some (.iunop .w32 .extend16s)
  else if op = 0xC2 then some (.iunop .w64 .extend8s)
  else if op = 0xC3 then some (.iunop .w64 .extend16s)
  else if op = 0xC4 then some (.iunop .w64 .extend32s)
  else if op = 0xD1 then some .refIsNull
  else none

/-- One-byte opcodes taking one `u32` index (the spec table `FVA.Wasm.Binary.idxOps`). -/
def idxOpOf (op : Nat) : Option (Nat → Instr) :=
  if op = 0x0C then some .br else if op = 0x0D then some .brIf
  else if op = 0x10 then some .call else if op = 0xD2 then some .refFunc
  else if op = 0x20 then some .localGet else if op = 0x21 then some .localSet
  else if op = 0x22 then some .localTee else if op = 0x23 then some .globalGet
  else if op = 0x24 then some .globalSet else if op = 0x25 then some .tableGet
  else if op = 0x26 then some .tableSet else none

/-- Load/store opcodes `0x28`–`0x3E` (the spec table `FVA.Wasm.Binary.memOps`). -/
def memOpOf : Nat → Option (MemArg → Instr)
  | 0x28 => some (.load .i32) | 0x29 => some (.load .i64)
  | 0x2A => some (.load .f32) | 0x2B => some (.load .f64)
  | 0x2C => some (.loadPacked .w32 .p8 .s) | 0x2D => some (.loadPacked .w32 .p8 .u)
  | 0x2E => some (.loadPacked .w32 .p16 .s) | 0x2F => some (.loadPacked .w32 .p16 .u)
  | 0x30 => some (.loadPacked .w64 .p8 .s) | 0x31 => some (.loadPacked .w64 .p8 .u)
  | 0x32 => some (.loadPacked .w64 .p16 .s) | 0x33 => some (.loadPacked .w64 .p16 .u)
  | 0x34 => some (.loadPacked .w64 .p32 .s) | 0x35 => some (.loadPacked .w64 .p32 .u)
  | 0x36 => some (.store .i32) | 0x37 => some (.store .i64)
  | 0x38 => some (.store .f32) | 0x39 => some (.store .f64)
  | 0x3A => some (.storePacked .w32 .p8) | 0x3B => some (.storePacked .w32 .p16)
  | 0x3C => some (.storePacked .w64 .p8) | 0x3D => some (.storePacked .w64 .p16)
  | 0x3E => some (.storePacked .w64 .p32)
  | _ => none

/-- Opcodes of features outside the profile, reported as unsupported rather than malformed. -/
def unsupportedOp (op : Nat) : Option String :=
  if op = 0xFD then some "SIMD (0xFD prefix)"
  else if op = 0xFE then some "threads/atomics (0xFE prefix)"
  else if op = 0xFB then some "GC (0xFB prefix)"
  else if 0x06 ≤ op ∧ op ≤ 0x0A ∨ op = 0x18 ∨ op = 0x19 ∨ op = 0x1F then
    some "exception handling"
  else if op = 0x12 ∨ op = 0x13 then some "tail calls"
  else if op = 0x14 ∨ op = 0x15 ∨ (0xD3 ≤ op ∧ op ≤ 0xD6) then some "typed function references"
  else none

/-- Read the zero byte that stands for memory index 0. -/
def zeroByte (r : Reader) : Res Unit := do
  let (b, r') ← r.byte
  if b.toNat = 0 then .ok ((), r') else r.unsup "multiple memories"

/-- `0xFC`-prefixed instructions (after the prefix byte). -/
def fcInstr (r : Reader) : Res Instr := do
  let (n, r) ← u32 r
  if n < 8 then
    let (dst, src, sx) :=
      match n with
      | 0 => (Width.w32, Width.w32, Sx.s) | 1 => (.w32, .w32, .u) | 2 => (.w32, .w64, .s)
      | 3 => (.w32, .w64, .u) | 4 => (.w64, .w32, .s) | 5 => (.w64, .w32, .u)
      | 6 => (.w64, .w64, .s) | _ => (.w64, .w64, .u)
    .ok (.cvtop (.truncSat dst src sx), r)
  else if n = 8 then do
    let (x, r) ← u32 r
    let ((), r) ← zeroByte r
    .ok (.memoryInit x, r)
  else if n = 9 then do
    let (x, r) ← u32 r
    .ok (.dataDrop x, r)
  else if n = 10 then do
    let ((), r) ← zeroByte r
    let ((), r) ← zeroByte r
    .ok (.memoryCopy, r)
  else if n = 11 then do
    let ((), r) ← zeroByte r
    .ok (.memoryFill, r)
  else if n = 12 then do
    let (y, r) ← u32 r
    let (x, r) ← u32 r
    .ok (.tableInit x y, r)
  else if n = 13 then do
    let (x, r) ← u32 r
    .ok (.elemDrop x, r)
  else if n = 14 then do
    let (x, r) ← u32 r
    let (y, r) ← u32 r
    .ok (.tableCopy x y, r)
  else if n = 15 then do
    let (x, r) ← u32 r
    .ok (.tableGrow x, r)
  else if n = 16 then do
    let (x, r) ← u32 r
    .ok (.tableSize x, r)
  else if n = 17 then do
    let (x, r) ← u32 r
    .ok (.tableFill x, r)
  else r.bad "illegal opcode"

/-- Instructions up to a terminator (`0x0B` end or `0x05` else); returns the terminator.
Structural on `fuel`; callers pass the remaining byte count (each instruction is ≥ 1 byte). -/
def instrs : Nat → Reader → Res (Instrs × Nat)
  | 0, r => r.bad "unexpected end"
  | fuel + 1, r => do
    let (b, r₁) ← r.byte
    let op := b.toNat
    if op = 0x0B ∨ op = 0x05 then .ok ((.nil, op), r₁) else do
    let (i, r₂) ← (instrAt fuel op r r₁ : Res Instr)
    let ((is, t), r₃) ← instrs fuel r₂
    .ok ((.cons i is, t), r₃)
where
  /-- One instruction with opcode `op` (already read; `r` points at the opcode). -/
  instrAt (fuel op : Nat) (r r₁ : Reader) : Res Instr :=
    match plainOpOf op with
    | some i => .ok (i, r₁)
    | none =>
    match idxOpOf op with
    | some mk => do
      let (x, r₂) ← u32 r₁
      .ok (mk x, r₂)
    | none =>
    match memOpOf op with
    | some mk => do
      let (m, r₂) ← memArg r₁
      .ok (mk m, r₂)
    | none =>
    if op = 0x02 ∨ op = 0x03 then do
      let (bt, r₂) ← blockType r₁
      let ((body, t), r₃) ← instrs fuel r₂
      if t = 0x0B then .ok ((if op = 0x02 then .block bt body else .loop bt body), r₃)
      else r.bad "else outside if"
    else if op = 0x04 then do
      let (bt, r₂) ← blockType r₁
      let ((thn, t), r₃) ← instrs fuel r₂
      if t = 0x0B then .ok (.if_ bt thn .nil, r₃) else do
      let ((els, t'), r₄) ← instrs fuel r₃
      if t' = 0x0B then .ok (.if_ bt thn els, r₄) else r.bad "duplicate else"
    else if op = 0x0E then do
      let (ls, r₂) ← vec u32 r₁
      let (l, r₃) ← u32 r₂
      .ok (.brTable ls l, r₃)
    else if op = 0x11 then do
      let (y, r₂) ← u32 r₁
      let (x, r₃) ← u32 r₂
      .ok (.callIndirect x y, r₃)
    else if op = 0x1C then do
      let (ts, r₂) ← vec valType r₁
      .ok (.select (some ts), r₂)
    else if op = 0xD0 then do
      let (t, r₂) ← refType r₁
      .ok (.refNull t, r₂)
    else if op = 0x3F then do
      let ((), r₂) ← zeroByte r₁
      .ok (.memorySize, r₂)
    else if op = 0x40 then do
      let ((), r₂) ← zeroByte r₁
      .ok (.memoryGrow, r₂)
    else if op = 0x41 then do
      let (n, r₂) ← sleb 5 32 r₁
      .ok (.iconst .w32 (n % 2 ^ 32).toNat, r₂)
    else if op = 0x42 then do
      let (n, r₂) ← sleb 10 64 r₁
      .ok (.iconst .w64 (n % 2 ^ 64).toNat, r₂)
    else if op = 0x43 then do
      let (z, r₂) ← leNat 4 r₁
      .ok (.fconst .w32 z, r₂)
    else if op = 0x44 then do
      let (z, r₂) ← leNat 8 r₁
      .ok (.fconst .w64 z, r₂)
    else if op = 0xFC then fcInstr r₁
    else match unsupportedOp op with
      | some what => r.unsup what
      | none => r.bad "illegal opcode"

/-- An expression: instructions terminated by `end`. -/
def expr (r : Reader) : Res Expr := do
  let ((is, t), r') ← instrs r.len r
  if t = 0x0B then .ok (is, r') else r.bad "else outside if"

end FVA.Wasm.Decode
