import FVA.Spec.Exec.Runtime

/-!
# Chunked memory (verified implementation)

A persistent binary trie over address bits: `z` = an all-zero subtree, `leaf c` = `2^W` bytes
packed little-endian in one `Nat` (byte `i` = `c / 256^i % 256`), `node l r` = the low half then
the high half. A depth-`d` trie covers `[0, 2^(d + W))`. Data only (no closures), so the kernel
reduces it and checkpoints print it; leaf width `2^W` is the perf protocol's parameter
(`docs/contracts/U26-machine.md` E4). `FVA.Proof.Exec.Chunks` relates it to `MemInst`.
-/

namespace FVA.Wasm.Exec.Machine

open FVA.Wasm FVA.Wasm.Exec

/-- `log₂` of the leaf width in bytes. -/
def W : Nat := 6

/-- Chunked bytes. -/
inductive Chunks where
  | z
  | leaf (c : Nat)
  | node (l r : Chunks)
  deriving Inhabited, Repr

namespace Chunks

/-- Byte `i` of a leaf. -/
def leafByte (c i : Nat) : Nat := c / 256 ^ i % 256

/-- Leaf `c` with byte `i` replaced by `b < 256`: the bytes below `i`, then `b`, then the bytes
above `i`. -/
def leafSet (c i b : Nat) : Nat := c % 256 ^ i + 256 ^ i * (b + 256 * (c / 256 ^ (i + 1)))

/-- The byte at address `a` of a depth-`d` trie (`a < 2^(d + W)`). -/
def get : Nat → Chunks → Nat → Nat
  | _, .z, _ => 0
  | _, .leaf c, a => leafByte c (a % 2 ^ W)
  | 0, .node _ _, _ => 0
  | d + 1, .node l r, a => bif Nat.testBit a (d + W) then get d r a else get d l a

/-- Set the byte at address `a` of a depth-`d` trie to `b < 256`. -/
def set : Nat → Chunks → Nat → Nat → Chunks
  | 0, t, a, b =>
    let c := match t with
      | .leaf c => c
      | _ => 0
    .leaf (leafSet c (a % 2 ^ W) b)
  | d + 1, t, a, b =>
    let (l, r) := match t with
      | .node l r => (l, r)
      | _ => (.z, .z)
    bif Nat.testBit a (d + W) then .node l (set d r a b) else .node (set d l a b) r

end Chunks

/-- An executable memory instance: pages, maximum, trie depth, bytes. -/
structure MMem where
  /-- Current size in pages. -/
  pages : Nat
  /-- Maximum size in pages. -/
  max : Option Nat
  /-- Trie depth: the trie covers `[0, 2^(depth + W))`. -/
  depth : Nat
  /-- Bytes; zero outside what was written. -/
  data : Chunks
  deriving Inhabited

namespace MMem

/-- `|data|`, the size in bytes. -/
def size (m : MMem) : Nat := m.pages * 65536

/-- The byte at address `a`; zero past the trie's reach. -/
def byte (m : MMem) (a : Nat) : Nat :=
  bif Nat.blt a (2 ^ (m.depth + W)) then m.data.get m.depth a else 0

/-- The little-endian number in the `k` bytes at `ea`. -/
def read (m : MMem) (ea : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => m.byte ea + 256 * m.read (ea + 1) k

/-- Store the `k` little-endian bytes of `v` at `ea` (inside the trie's reach). -/
def write (m : MMem) (ea : Nat) : Nat → Nat → MMem
  | 0, _ => m
  | k + 1, v => { m with data := m.data.set m.depth ea (v % 256) }.write (ea + 1) k (v / 256)

/-- The `n` bytes from `src`. -/
def readBytes (m : MMem) (src : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => m.byte src :: m.readBytes (src + 1) n

/-- Write bytes `bs` (each `< 256`) from `dst`. -/
def writeBytes (m : MMem) (dst : Nat) : List Nat → MMem
  | [] => m
  | b :: bs => { m with data := m.data.set m.depth dst b }.writeBytes (dst + 1) bs

/-- `n` bytes `b < 256` from `dst` (`memory.fill`). -/
def fill (m : MMem) (dst n b : Nat) : MMem := m.writeBytes dst (List.replicate n b)

/-- `n` bytes from `src` to `dst`, overlap allowed (`memory.copy`: the source is read before
any write, which equals the spec's ascending copy when `dst ≤ src` and descending otherwise). -/
def copy (m : MMem) (dst src n : Nat) : MMem := m.writeBytes dst (m.readBytes src n)

/-- Bytes `bs` from `dst` (`memory.init` of a data segment slice). -/
def init (m : MMem) (dst : Nat) (bs : List UInt8) : MMem := m.writeBytes dst (bs.map UInt8.toNat)

/-- The smallest depth whose trie covers `n` bytes. -/
def depthFor (n : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => bif Nat.ble n (2 ^ W) then 0 else depthFor ((n + 1) / 2) fuel + 1

/-- Raise the depth to `d'` (≥ depth), the old trie as the low part. -/
def deepen (m : MMem) : Nat → MMem
  | 0 => m
  | k + 1 => { m with depth := m.depth + 1, data := .node m.data .z }.deepen k

/-- `growmem(m, n)`: `n` zero pages appended; `none` past 2^16 pages or the maximum. -/
def grow (m : MMem) (n : Nat) : Option MMem :=
  let len := m.pages + n
  bif Nat.blt (2 ^ 16) len || m.max.any (Nat.blt · len) then none
  else
    let d := depthFor (len * 65536) 64
    some ({ m with pages := len }.deepen (d - m.depth))

/-- A fresh memory of `pages` zero pages. -/
def alloc (pages : Nat) (max : Option Nat) : MMem :=
  { pages, max, depth := depthFor (pages * 65536) 64, data := .z }

/-- The spec memory this one denotes. -/
def abs (m : MMem) : MemInst :=
  { pages := m.pages, max := m.max, byte := fun a => UInt8.ofNat (m.byte a) }

end MMem

end FVA.Wasm.Exec.Machine
