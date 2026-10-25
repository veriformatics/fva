import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

noncomputable def fresh : Store × ModuleInst := allocModule {} Lifted.module [] [] []

def encoderInput : List UInt8 := [97,98,99,100,101,97,98,99,100,87,88,89,90]
def encoderOutput : List UInt8 := [80,97,98,99,100,101,5,0,64,87,88,89,90]
def validBlock : List UInt8 := [16,65,1,0,128,66,67,68,69,70,71,72,73]
def decodedContent : List UInt8 := [65,65,65,65,65,66,67,68,69,70,71,72,73]

/-- Exactly the documented hash-table initialization, then input, in five pages. -/
noncomputable def encoderStore : Store :=
  { fresh.1 with mems := [{ pages := 5, max := none, byte := fun a =>
      if a < 262144 then (if a % 4 < 2 then 0 else 255)
      else if a < 262157 then encoderInput[a - 262144]! else 0 }] }

def bytesAt (s : Store) (p : Nat) (bs : List UInt8) : Prop :=
  ∃ m, s.mems[0]? = some m ∧ ∀ i, i < bs.length → m.byte (p + i) = bs[i]!

/-- Necessary LZ4 end conditions for a block with a match: five final literals,
    and the last match starts at least twelve decoded bytes before the end. -/
def endConditions (decodedSize lastMatchStart finalLiterals : Nat) : Prop :=
  5 ≤ finalLiterals ∧ lastMatchStart + 12 ≤ decodedSize

/-- A sufficient validity certificate for two sequences without length extensions.
    The first sequence has literals and a match; the second has only literals.
    Match bytes use the documented forward, overlapping-copy interpretation. -/
def shortValid (block decoded : List UInt8) : Prop :=
  ∃ (lit tail : List UInt8) (off len : Nat),
    0 < lit.length ∧ lit.length < 15 ∧ tail.length < 15 ∧
    0 < off ∧ off ≤ lit.length ∧ off < 65536 ∧ 4 ≤ len ∧ len < 19 ∧
    block = [UInt8.ofNat (16 * lit.length + (len - 4))] ++ lit ++
      [UInt8.ofNat off, UInt8.ofNat (off / 256), UInt8.ofNat (16 * tail.length)] ++ tail ∧
    decoded = lit ++ (List.range len).map (fun i => lit[lit.length - off + i % off]!) ++ tail ∧
    endConditions decoded.length lit.length tail.length

/-- Preparation is a fresh instance, growable from one to five pages, with all
    65536 hash words equal to -65536 and the stated thirteen input bytes. -/
def preparation : Prop :=
  (∀ H, Instance Lifted.module H fresh.1 fresh.2) ∧
  (∃ m m', fresh.1.mems[0]? = some m ∧ m.grow 4 = some m' ∧ m'.pages = 5) ∧
  (∀ i, i < 65536 → ∃ m, encoderStore.mems[0]? = some m ∧ m.read (4*i) 4 = 4294901760) ∧
  bytesAt encoderStore 262144 encoderInput

/-- R1 counterexample: the encoder returns the displayed 13-byte block.
    Its unambiguous parse has five literals, offset 5, match length 4, then
    four final literals: both mandatory end conditions fail. -/
def r1 : Prop :=
  (∀ H, CallReturns H encoderStore fresh.2 "lz4BlockEncode"
    [.i32 262144, .i32 13, .i32 262200]
    (fun s vs => vs = [.i32 13] ∧ bytesAt s 262200 encoderOutput)) ∧
  ¬ endConditions 13 5 4

/-- R2 counterexample: a certified valid block denotes thirteen bytes, but
    decoding at input 100 and disjoint output 0 returns one, writing only A. -/
def r2 : Prop :=
  shortValid validBlock decodedContent ∧ decodedContent.length = 13 ∧
  ∀ H, CallReturns H (fresh.1.withBytes 100 validBlock) fresh.2 "lz4BlockDecode"
    [.i32 100, .i32 13, .i32 0]
    (fun s vs => vs = [.i32 1] ∧ bytesAt s 0 [65,0,0,0,0,0,0,0,0,0,0,0,0])

/-- R3 counterexample: the valid empty block [0], wholly in memory's final
    byte, traps. The decoder attempts an offset read at 65536 (outside it). -/
def r3 : Prop :=
  ∀ H, CallTraps H (fresh.1.withBytes 65535 [0]) fresh.2 "lz4BlockDecode"
    [.i32 65535, .i32 1, .i32 0] (fun _ => True)

/-- R3 also has an observable out-of-block read without a trap: the same
    one-byte block [0] returns 0 or 4 depending only on the following byte,
    which lies outside the supplied block. Both runs have ample memory. -/
def r3_dependence : Prop :=
  (∀ H, CallReturns H (fresh.1.withBytes 100 [0,0,0]) fresh.2 "lz4BlockDecode"
    [.i32 100, .i32 1, .i32 1000]
    (fun s vs => vs = [.i32 0] ∧ bytesAt s 1000 [0,0,0,0])) ∧
  (∀ H, CallReturns H (fresh.1.withBytes 100 [0,1,0]) fresh.2 "lz4BlockDecode"
    [.i32 100, .i32 1, .i32 1000]
    (fun s vs => vs = [.i32 4] ∧ bytesAt s 1000 [0,0,0,0]))

end Proofs
