import Proofs.Artifact
import Proofs.Format

namespace Verification

structure Case where
  name : String
  input : List Nat
  cap : Nat
  src : Nat := 131072
  dst : Nat := 262144
  witness : Option LZ4.Block
  deriving Repr

def Case.returnWord (c : Case) : Nat :=
  match c.witness with | none => 4294967295 | some b => b.decode.length

def Case.output (c : Case) : List Nat :=
  match c.witness with | none => [] | some b => b.decode

def Case.contract (c : Case) : Bool :=
  131072 ≤ c.src && c.src+c.input.length ≤ 2097152 &&
  131072 ≤ c.dst && c.dst+c.cap ≤ 2097152 &&
  (c.src+c.input.length ≤ c.dst || c.dst+c.cap ≤ c.src) && LZ4.bytes c.input

def start (mem : Wasm.Memory) (src dst n cap : Nat) : Wasm.State :=
  { locals := #[src, dst, n, cap] ++ Array.replicate Artifact.localCount 0
    mem := mem }

def Case.initial (c : Case) : Wasm.State :=
  start ((Wasm.Memory.writeBytes {} Artifact.dataAddress Artifact.dataBytes).writeBytes
            c.src c.input) c.src c.dst c.input.length c.cap

def Case.execute (c : Case) : Wasm.State :=
  Wasm.run Artifact.code 100000 c.initial

/-- Checks the buffer contract, termination without traps/unsupported instructions,
    R1's entire access trace, unchanged input, and exact return/output. Successful
    cases also carry an independent R3 parsing/decoding witness. -/
def Case.certify (c : Case) : Bool := Id.run do
  if !c.contract then return false
  let s := c.execute
  if s.status != .returned c.returnWord then return false
  if !s.accesses.all (Wasm.confined c.src c.dst c.input.length c.cap) then return false
  if s.mem.readBytes c.src c.input.length != c.input then return false
  match c.witness with
  | none => return true
  | some b =>
    return b.relaxed && b.encode == c.input && b.decode.length ≤ c.cap &&
           s.mem.readBytes c.dst b.decode.length == b.decode

def literalBlock (n : Nat) : LZ4.Block :=
  { lastLiterals := (List.range n).map (fun i => (i*37+11)%256) }

def matchBlock (lit off len final : Nat) : LZ4.Block :=
  { sequences := [⟨(List.range lit).map (fun i => (i*37+11)%256), off, len⟩]
    lastLiterals := (List.range final).map (fun i => (i*13+97)%256) }

def strictBlocks : List (String × LZ4.Block × Nat) :=
  (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 7 :: 8 :: 14 :: 15 :: 16 :: 17 ::
    31 :: 32 :: 33 :: 269 :: 270 :: 525 :: []).map
    (fun n => ("literals_" ++ toString n, literalBlock n, n)) ++
  [("slow_offset1", matchBlock 1 1 7 5, 13),
   ("slow_overlap", matchBlock 2 2 7 5, 14),
   ("hot_overlap", matchBlock 7 1 7 8, 64),
   ("hot_disjoint", matchBlock 7 7 4 8, 64),
   ("slow_wild32", matchBlock 32 32 4 8, 128),
   ("slow_wild64", matchBlock 64 64 40 8, 256),
   ("bulk_match", matchBlock 100 100 80 8, 220),
   ("long_match", matchBlock 1 1 274 5, 280),
   ("two_sequences",
    { sequences := [⟨[65,66,67,68,69,70,71], 7, 4⟩, ⟨[72], 2, 7⟩]
      lastLiterals := [80,81,82,83,84,85,86,87] }, 128)]

def strictCases : List Case := strictBlocks.map fun (name, b, cap) =>
  ⟨name, b.encode, cap, 131072, 262144, some b⟩

def relaxedCases : List Case :=
  let b₁ : LZ4.Block := { sequences := [⟨[65], 1, 4⟩] }
  let b₂ : LZ4.Block := { sequences := [⟨[65], 1, 4⟩], lastLiterals := [66] }
  [⟨"end_conditions_only_1", b₁.encode, 5, 131072, 262144, some b₁⟩,
   ⟨"end_conditions_only_2", b₂.encode, 35, 131072, 262144, some b₂⟩]

def rejectedCases : List Case :=
  [("no_token", [], 0),
   ("truncated_literal_extension", [240], 64),
   ("unterminated_literal_extension", [240,255], 64),
   ("truncated_literals", [32,65], 64),
   ("truncated_offset", [16,65,1], 64),
   ("offset_zero", [16,65,0,0,80,66,67,68,69,70], 64),
   ("offset_before_start", [16,65,2,0,80,66,67,68,69,70], 64),
   ("no_initial_history", [0,1,0,80,66,67,68,69,70], 64),
   ("truncated_match_extension", [31,65,1,0], 64),
   ("unterminated_match_extension", [31,65,1,0,255], 512),
   ("literal_output_too_small", [32,65,66], 1),
   ("match_output_too_small", [16,65,1,0,0], 4),
   ("hot_offset_zero", [112,65,66,67,68,69,70,71,0,0,128,80,81,82,83,84,85,86,87], 64),
   ("hot_offset_before_start", [112,65,66,67,68,69,70,71,8,0,128,80,81,82,83,84,85,86,87], 64)].map
    fun (name, input, cap) => ⟨name, input, cap, 131072, 262144, none⟩

def placements (c : Case) : List Case :=
  [c,
   {c with src := 2097152 - max c.input.length 1, dst := 131072},
   {c with src := 131072+c.cap, dst := 131072},
   {c with src := 131072, dst := 131072+c.input.length}]

/-- Exhausts every possible one-byte input at capacities zero and thirty-five. -/
def oneByteCases : List Case := (List.range 256).flatMap fun token =>
  [0,35].map fun cap =>
    { name := "one_byte_" ++ toString token ++ "_cap_" ++ toString cap
      input := [token], cap := cap
      witness := if token < 16 then some {lastNibble := token} else none }

def cases : List Case :=
  (strictCases ++ relaxedCases ++ rejectedCases ++ oneByteCases).flatMap placements

end Verification
