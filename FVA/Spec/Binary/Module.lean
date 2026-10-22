import FVA.Spec.Binary.Instr

/-!
# Modules in the binary format (reviewed spec)

Spec §5.5. `ModuleB m bs` reads: the complete file `bs` encodes the module `m`. Custom sections
may appear between any sections and carry no meaning; absent and empty sections decode alike.
-/

namespace FVA.Wasm.Binary

open FVA.Wasm

/-- `section_N(B)`: id byte, `u32` content size, content (spec §5.5.2). -/
def SectionB {α : Type} (id : UInt8) (R : α → List UInt8 → Prop) (a : α) (bs : List UInt8) :
    Prop :=
  ∃ sb cont, R a cont ∧ ULeb 32 cont.length sb ∧ bs = id :: sb ++ cont

/-- A custom section: id 0, a name, then any bytes (spec §5.5.3). -/
def CustomB (bs : List UInt8) : Prop :=
  ∃ (nm : String) (nb rest : List UInt8), SectionB 0 (fun _ cont => Name nm nb ∧ cont = nb ++ rest)
    () bs

/-- Any number of custom sections. -/
inductive CustomsB : List UInt8 → Prop where
  | nil : CustomsB []
  | cons {b₁ b₂ : List UInt8} (h : CustomB b₁) (hs : CustomsB b₂) : CustomsB (b₁ ++ b₂)

/-- An optional `vec` section: absent (empty list) or present with section id `id`. -/
def VecSecB {α : Type} (id : UInt8) (R : α → List UInt8 → Prop) (xs : List α)
    (bs : List UInt8) : Prop :=
  (xs = [] ∧ bs = []) ∨ SectionB id (Vec R) xs bs

/-- An optional single-value section (start, data count). -/
def OptSecB {α : Type} (id : UInt8) (R : α → List UInt8 → Prop) (x : Option α)
    (bs : List UInt8) : Prop :=
  match x with
  | none => bs = []
  | some a => SectionB id R a bs

/-- Index into a vector, encoded as `u32`. -/
def IdxB (x : Nat) (bs : List UInt8) : Prop := ULeb 32 x bs

/-- Import descriptions (spec §5.5.5). -/
def ImportDescB : ImportDesc → List UInt8 → Prop
  | .func x, bs => ∃ b, IdxB x b ∧ bs = 0x00 :: b
  | .table t, bs => ∃ b, TableTypeB t b ∧ bs = 0x01 :: b
  | .mem t, bs => ∃ b, LimitsB t b ∧ bs = 0x02 :: b
  | .global t, bs => ∃ b, GlobalTypeB t b ∧ bs = 0x03 :: b

/-- Imports: module name, field name, description (spec §5.5.5). -/
def ImportB (im : Import) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂ b₃, Name im.module b₁ ∧ Name im.name b₂ ∧ ImportDescB im.desc b₃ ∧
    bs = b₁ ++ b₂ ++ b₃

/-- Globals: type and initializer (spec §5.5.9). -/
def GlobalB (g : Global) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, GlobalTypeB g.type b₁ ∧ ExprB g.init b₂ ∧ bs = b₁ ++ b₂

/-- Export descriptions (spec §5.5.10). -/
def ExportDescB : ExportDesc → List UInt8 → Prop
  | .func x, bs => ∃ b, IdxB x b ∧ bs = 0x00 :: b
  | .table x, bs => ∃ b, IdxB x b ∧ bs = 0x01 :: b
  | .mem x, bs => ∃ b, IdxB x b ∧ bs = 0x02 :: b
  | .global x, bs => ∃ b, IdxB x b ∧ bs = 0x03 :: b

/-- Exports: name and description (spec §5.5.10). -/
def ExportB (ex : Export) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, Name ex.name b₁ ∧ ExportDescB ex.desc b₂ ∧ bs = b₁ ++ b₂

/-- Element kind `0x00` = `funcref` (spec §5.5.12). -/
def ElemKindB (t : RefType) (bs : List UInt8) : Prop := t = .funcref ∧ bs = [0x00]

/-- Function indices as `(ref.func y) end` initializers. -/
def funcInits (ys : List Nat) : List Expr := ys.map fun y => .cons (Instr.refFunc y) .nil

/-- Element segments: the eight encodings selected by a `u32` flag (spec §5.5.12). -/
inductive ElemB : Elem → List UInt8 → Prop where
  | e0 {off : Expr} {ys : List Nat} {bf be bv : List UInt8} (hf : ULeb 32 0 bf) (he : ExprB off be)
      (hv : Vec IdxB ys bv) :
      ElemB { type := .funcref, init := funcInits ys, mode := .active 0 off } (bf ++ be ++ bv)
  | e1 {t : RefType} {ys : List Nat} {bf bk bv : List UInt8} (hf : ULeb 32 1 bf)
      (hk : ElemKindB t bk) (hv : Vec IdxB ys bv) :
      ElemB { type := t, init := funcInits ys, mode := .passive } (bf ++ bk ++ bv)
  | e2 {x : Nat} {off : Expr} {t : RefType} {ys : List Nat} {bf bx be bk bv : List UInt8}
      (hf : ULeb 32 2 bf) (hx : IdxB x bx) (he : ExprB off be) (hk : ElemKindB t bk)
      (hv : Vec IdxB ys bv) :
      ElemB { type := t, init := funcInits ys, mode := .active x off } (bf ++ bx ++ be ++ bk ++ bv)
  | e3 {t : RefType} {ys : List Nat} {bf bk bv : List UInt8} (hf : ULeb 32 3 bf)
      (hk : ElemKindB t bk) (hv : Vec IdxB ys bv) :
      ElemB { type := t, init := funcInits ys, mode := .declarative } (bf ++ bk ++ bv)
  | e4 {off : Expr} {els : List Expr} {bf be bv : List UInt8} (hf : ULeb 32 4 bf)
      (he : ExprB off be) (hv : Vec ExprB els bv) :
      ElemB { type := .funcref, init := els, mode := .active 0 off } (bf ++ be ++ bv)
  | e5 {t : RefType} {els : List Expr} {bf bt bv : List UInt8} (hf : ULeb 32 5 bf)
      (ht : RefTypeB t bt) (hv : Vec ExprB els bv) :
      ElemB { type := t, init := els, mode := .passive } (bf ++ bt ++ bv)
  | e6 {x : Nat} {off : Expr} {t : RefType} {els : List Expr} {bf bx be bt bv : List UInt8}
      (hf : ULeb 32 6 bf) (hx : IdxB x bx) (he : ExprB off be) (ht : RefTypeB t bt)
      (hv : Vec ExprB els bv) :
      ElemB { type := t, init := els, mode := .active x off } (bf ++ bx ++ be ++ bt ++ bv)
  | e7 {t : RefType} {els : List Expr} {bf bt bv : List UInt8} (hf : ULeb 32 7 bf)
      (ht : RefTypeB t bt) (hv : Vec ExprB els bv) :
      ElemB { type := t, init := els, mode := .declarative } (bf ++ bt ++ bv)

/-- Data segments: three encodings selected by a `u32` flag (spec §5.5.14). -/
inductive DataB : Data → List UInt8 → Prop where
  | d0 {off : Expr} {init : List UInt8} {bf be bv : List UInt8} (hf : ULeb 32 0 bf)
      (he : ExprB off be) (hv : Vec Byte init bv) :
      DataB { init := init, mode := .active 0 off } (bf ++ be ++ bv)
  | d1 {init : List UInt8} {bf bv : List UInt8} (hf : ULeb 32 1 bf) (hv : Vec Byte init bv) :
      DataB { init := init, mode := .passive } (bf ++ bv)
  | d2 {x : Nat} {off : Expr} {init : List UInt8} {bf bx be bv : List UInt8}
      (hf : ULeb 32 2 bf) (hx : IdxB x bx) (he : ExprB off be) (hv : Vec Byte init bv) :
      DataB { init := init, mode := .active x off } (bf ++ bx ++ be ++ bv)

/-- A run of locals: `n:u32 t:valtype` (spec §5.5.13). -/
def LocalsB (g : Nat × ValType) (bs : List UInt8) : Prop :=
  ∃ b₁ b₂, ULeb 32 g.1 b₁ ∧ ValTypeB g.2 b₂ ∧ bs = b₁ ++ b₂

/-- A code entry: `size:u32` then local runs and the body; at most 2^32 − 1 locals in total
(spec §5.5.13). -/
def CodeB (c : List ValType × Expr) (bs : List UInt8) : Prop :=
  ∃ (groups : List (Nat × ValType)) (bsz bl be : List UInt8),
    Vec LocalsB groups bl ∧ ExprB c.2 be ∧
    (groups.map Prod.fst).sum < 2 ^ 32 ∧
    c.1 = groups.flatMap (fun g => List.replicate g.1 g.2) ∧
    ULeb 32 (bl ++ be).length bsz ∧ bs = bsz ++ bl ++ be

mutual
/-- The instruction uses a data index (`memory.init`, `data.drop`), possibly nested. -/
inductive UsesData : Instr → Prop where
  | init (x : Nat) : UsesData (.memoryInit x)
  | drop (x : Nat) : UsesData (.dataDrop x)
  | block {bt : BlockType} {body : Instrs} (h : UsesDataS body) : UsesData (.block bt body)
  | loop {bt : BlockType} {body : Instrs} (h : UsesDataS body) : UsesData (.loop bt body)
  | thn {bt : BlockType} {thn els : Instrs} (h : UsesDataS thn) : UsesData (.if_ bt thn els)
  | els {bt : BlockType} {thn els : Instrs} (h : UsesDataS els) : UsesData (.if_ bt thn els)
/-- Some instruction of the sequence uses a data index. -/
inductive UsesDataS : Instrs → Prop where
  | head {i : Instr} {is : Instrs} (h : UsesData i) : UsesDataS (.cons i is)
  | tail {i : Instr} {is : Instrs} (h : UsesDataS is) : UsesDataS (.cons i is)
end

/-- The magic number `\0asm` and version 1 (spec §5.5.16). -/
def preamble : List UInt8 := [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]

/-- `ModuleB m bs`: the file `bs` encodes the module `m` (spec §5.5.16). The function and code
sections have equal length; a data count, when present, equals the number of data segments;
code may use data indices only when the data count section is present. -/
def ModuleB (m : Module) (bs : List UInt8) : Prop :=
  ∃ (typeIdxs : List Nat) (codes : List (List ValType × Expr)) (dataCount : Option Nat)
    (c₀ s₁ c₁ s₂ c₂ s₃ c₃ s₄ c₄ s₅ c₅ s₆ c₆ s₇ c₇ s₈ c₈ s₉ c₉ s₁₂ c₁₂ s₁₀ c₁₀ s₁₁ c₁₁ :
      List UInt8),
    CustomsB c₀ ∧ VecSecB 1 FuncTypeB m.types s₁ ∧ CustomsB c₁ ∧
    VecSecB 2 ImportB m.imports s₂ ∧ CustomsB c₂ ∧
    VecSecB 3 IdxB typeIdxs s₃ ∧ CustomsB c₃ ∧
    VecSecB 4 TableTypeB m.tables s₄ ∧ CustomsB c₄ ∧
    VecSecB 5 LimitsB m.mems s₅ ∧ CustomsB c₅ ∧
    VecSecB 6 GlobalB m.globals s₆ ∧ CustomsB c₆ ∧
    VecSecB 7 ExportB m.exports s₇ ∧ CustomsB c₇ ∧
    OptSecB 8 IdxB m.start s₈ ∧ CustomsB c₈ ∧
    VecSecB 9 ElemB m.elems s₉ ∧ CustomsB c₉ ∧
    OptSecB 12 (ULeb 32) dataCount s₁₂ ∧ CustomsB c₁₂ ∧
    VecSecB 10 CodeB codes s₁₀ ∧ CustomsB c₁₀ ∧
    VecSecB 11 DataB m.datas s₁₁ ∧ CustomsB c₁₁ ∧
    typeIdxs.length = codes.length ∧
    m.funcs = List.zipWith (fun t c => { type := t, locals := c.1, body := c.2 }) typeIdxs codes ∧
    (∀ n, dataCount = some n → n = m.datas.length) ∧
    (dataCount = none → ∀ c ∈ codes, ¬ UsesDataS c.2) ∧
    bs = preamble ++ c₀ ++ s₁ ++ c₁ ++ s₂ ++ c₂ ++ s₃ ++ c₃ ++ s₄ ++ c₄ ++ s₅ ++ c₅ ++ s₆ ++ c₆ ++
      s₇ ++ c₇ ++ s₈ ++ c₈ ++ s₉ ++ c₉ ++ s₁₂ ++ c₁₂ ++ s₁₀ ++ c₁₀ ++ s₁₁ ++ c₁₁

end FVA.Wasm.Binary
