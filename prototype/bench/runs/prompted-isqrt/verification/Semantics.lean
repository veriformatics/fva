import Std.Tactic

namespace Wasm

-- Exact module envelope: one (i32)->i32 function, exported as isqrt;
-- one page of unused memory; locals i64,i32,i32,i64,i32; 72 code bytes.
def envelope : List Nat :=
  [0,97,115,109,1,0,0,0,1,6,1,96,1,127,1,127,3,2,1,0,
   5,3,1,0,1,7,18,2,6,109,101,109,111,114,121,2,0,5,105,115,
   113,114,116,0,0,10,83,1,81,4,1,126,2,127,1,126,1,127]

inductive Config where
  | live (pc : Nat) (locals stack labels : List Nat)
  | done (result : Nat)

-- Nonnegative signed LEB128 subset, sufficient for every shipped constant.
def immediate : Nat → List Nat → Option (Nat × Nat)
  | 0, _ => none
  | k+1, b::bs =>
    if b < 64 then some (b,1)
    else if 128 ≤ b ∧ b < 256 then do
      let (v,len) ← immediate k bs
      some (b-128 + 128*v, len+1)
    else none
  | _, [] => none

-- Small-step semantics for the actual opcode subset. Stack top is the head.
-- Words are natural numbers; every arithmetic instruction uses Wasm wrapping.
def step (code : List Nat) : Config → Option Config
  | .done r => some (.done r)
  | .live pc ls st labels =>
    let next := fun skip ls st labels => some (Config.live (pc+skip) ls st labels)
    let binary := fun f => match st with
      | b::a::rest => next 1 ls (f a b :: rest) labels
      | _ => none
    match code.drop pc with
    | 0x20::k::_ => do let v ← ls[k]?; next 2 ls (v::st) labels
    | 0x21::k::_ => do
      let _ ← ls[k]?
      let v::rest := st | none
      next 2 (ls.set k v) rest labels
    | 0x22::k::_ => do
      let _ ← ls[k]?
      let v::_ := st | none
      next 2 (ls.set k v) st labels
    | 0x41::bs => do
      let (v,len) ← immediate 5 bs
      next (1+len) ls ((v % 2^32)::st) labels
    | 0xad::_ => match st with
      | a::rest => next 1 ls ((a % 2^32)::rest) labels
      | _ => none
    | 0x6a::_ => binary (fun a b => (a+b) % 2^32)
    | 0x6b::_ => binary (fun a b => (a+2^32-b) % 2^32)
    | 0x76::_ => binary (fun a b => a / 2^(b % 32))
    | 0x7e::_ => binary (fun a b => (a*b) % 2^64)
    | 0x4b::_ | 0x56::_ => binary (fun a b => if b < a then 1 else 0)
    | 0x1b::_ => match st with
      | c::b::a::rest => next 1 ls ((if c = 0 then b else a)::rest) labels
      | _ => none
    | 0x03::0x40::_ => next 2 ls st ((pc+2)::labels)
    | 0x0d::0::_ => match st, labels with
      | c::rest, target::_ =>
        if c = 0 then next 2 ls rest labels
        else some (.live target ls rest labels)
      | _, _ => none
    | 0x0b::_ => match labels, st with
      | _::rest, _ => next 1 ls st rest
      | [], [r] => some (.done r)
      | _, _ => none
    | _ => none

-- Finite reflexive/transitive closure of the concrete byte-level step.
inductive Runs (code : List Nat) : Config → Config → Prop where
  | refl (c) : Runs code c c
  | next {a b c} : step code a = some b → Runs code b c → Runs code a c

-- Invocation of the actual export; a derivation is a finite returning trace.
def invoke (bytes : List Nat) (n r : Nat) : Prop :=
  bytes.take 58 = envelope ∧ bytes.length = 130 ∧ n < 2^32 ∧
    Runs (bytes.drop 58) (.live 0 [n,0,0,0,0,0] [] []) (.done r)

def IsSqrt (n r : Nat) : Prop :=
  r*r ≤ n ∧ ∀ s : Nat, s*s ≤ n → s ≤ r

end Wasm
