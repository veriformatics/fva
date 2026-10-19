import Init
namespace SatAdd
-- This is a deliberately partial Wasm semantics: unsupported bytes fail closed.
-- Stack heads are stack tops; locals 0,1 are arguments, local 2 is zero.
abbrev Word := BitVec 32

def execute : Nat → List Nat → (Nat → Word) → List Word → Option Word
  | 0, _, _, _ => none
  | _ + 1, [0x0b], _, [v] => some v                         -- end
  | n + 1, 0x20 :: i :: code, locals, stack =>              -- local.get
      if i < 3 then execute n code locals (locals i :: stack) else none
  | n + 1, 0x22 :: i :: code, locals, v :: stack =>         -- local.tee
      if i < 3 then execute n code (fun j => if j = i then v else locals j)
        (v :: stack) else none
  | n + 1, 0x41 :: 0x80 :: 0x80 :: 0x80 :: 0x80 :: 0x78 :: code, locals, stack =>
      execute n code locals (2147483648 :: stack)           -- i32.const -2^31
  | n + 1, 0x41 :: k :: code, locals, stack =>              -- positive one-byte SLEB
      if k < 64 then execute n code locals (BitVec.ofNat 32 k :: stack) else none
  | n + 1, 0x6a :: code, locals, y :: x :: stack =>         -- i32.add
      execute n code locals ((x + y) :: stack)
  | n + 1, 0x73 :: code, locals, y :: x :: stack =>         -- i32.xor
      execute n code locals ((x ^^^ y) :: stack)
  | n + 1, 0x75 :: code, locals, y :: x :: stack =>         -- i32.shr_s
      execute n code locals (x.sshiftRight (y.toNat % 32) :: stack)
  | n + 1, 0x48 :: code, locals, y :: x :: stack =>         -- i32.lt_s
      execute n code locals ((if x.slt y then 1 else 0) :: stack)
  | n + 1, 0x1b :: code, locals, c :: y :: x :: stack =>    -- select
      execute n code locals ((if c = 0 then y else x) :: stack)
  | _, _, _, _ => none

-- Exact supported module envelope: magic/version; type (i32,i32)->i32;
-- one function of type 0; one memory (min 1); exports memory and sat_add=func 0;
-- one 35-byte function body with one zero-initialized i32 local.
def envelope : List Nat :=
  [0,97,115,109,1,0,0,0,1,7,1,96,2,127,127,1,127,3,2,1,0,
   5,3,1,0,1,7,20,2,6,109,101,109,111,114,121,2,0,7,
   115,97,116,95,97,100,100,0,0,10,37,1,35,1,1,127]

def invoke (bytes : List Nat) (a b : Word) : Option Word :=
  if bytes.length = 87 ∧ bytes.take 55 = envelope then
    execute 32 (bytes.drop 55) (fun i => if i = 0 then a else if i = 1 then b else 0) []
  else none

-- Mathematical integers, NOT wrapping addition, express the README's R1--R3.
def Requirements (bytes : List Nat) : Prop :=
  ∀ a b : Word, ∃ r : Word, invoke bytes a b = some r ∧
    (-2147483648 ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ 2147483647 →
      r.toInt = a.toInt + b.toInt) ∧
    (2147483647 < a.toInt + b.toInt → r.toInt = 2147483647) ∧
    (a.toInt + b.toInt < -2147483648 → r.toInt = -2147483648)
end SatAdd
