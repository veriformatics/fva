import FVA.Proof.Wasi.WfRun

/-!
# WASI model examples (U29a T5)

Each expected value comes from a source, never from running `exec`: WITX (`Wf` =
`wasi_snapshot_preview1.witx`, `Wt` = `typenames.witx` at `fae981ba`), wasmtime 50.0.0
`crates/wasi/src/p1.rs` (`p1:`), a pinned-wasmtime probe (`FVATest/Wasi/probes/`: command + observed
output per probe), or the contract's `E` text (`docs/contracts/U29a-wasi.md`) where
`E` departs from wasmtime. Every example is a kernel `decide`.

World: args `p x`, env `K=V`, stdin `in`, clocks realtime 100 + monotonic 200, one preopen `.` =
`{f: "abc", d: {g: ""}, e: {}}` (nodes: `.` 0, `f` 1, `d` 2, `g` 3, `e` 4; serial = node + 1);
fds 0–2 stdio, 3 = the preopen.
-/

namespace FVA.Wasi.Examples

open FVA.Wasm FVA.Wasm.Exec FVA.Wasi

/-- ASCII bytes. -/
def b (s : String) : Bytes := s.toList.map fun c => c.toNat.toUInt8

/-- The example world (above). -/
def σ₀ : State :=
  State.init [b "p", b "x"] [b "K=V"] (b "in")
    [(b ".", .dir [(b "f", .file (b "abc")), (b "d", .dir [(b "g", .file [])]), (b "e", .dir [])])]
    [100, 200, 0, 0]

/-- One page holding `bs` at the given addresses, zero elsewhere. -/
def page (bs : List (Nat × Bytes)) : MemInst :=
  ⟨1, none, fun a => (bs.findSome? fun w =>
    if w.1 ≤ a ∧ a < w.1 + w.2.length then some (w.2.getD (a - w.1) 0) else none).getD 0⟩

/-- An iovec array at its address: (buffer, length) pairs, 8 bytes each. -/
def iov (vs : List (Nat × Nat)) : Bytes := vs.flatMap fun v => le 4 v.1 ++ le 4 v.2

/-- The arguments as values of the call's parameter types. -/
def vals (c : Call) (args : List Nat) : List Val :=
  (args.zip c.info.2).map fun a =>
    if a.2 then .i64 (BitVec.ofNat 64 a.1) else .i32 (BitVec.ofNat 32 a.1)

/-- Call `c` under `E`'s choices on world `σ` with memory `mem`: the successor world, the errno
(`none` = an exit or trap) and the memory after. -/
def call (σ : State) (mem : List (Nat × Bytes)) (c : Call) (args : List Nat) (ch : Choice := {}) :
    State × Option Nat × MemInst :=
  match exec σ c { mems := [page mem] } 0 (vals c args) ch with
  | (τ, .returned s [.i32 e]) => (τ, some e.toNat, (s.mems.headD (page [])))
  | (τ, .returned s _) => (τ, none, (s.mems.headD (page [])))
  | (τ, .trapped s) => (τ, none, (s.mems.headD (page [])))
  | (τ, .diverged) => (τ, none, page [])

/-- Call `c` in the profile domain? -/
def ok (σ : State) (mem : List (Nat × Bytes)) (c : Call) (args : List Nat) : Bool :=
  inProfile σ c { mems := [page mem] } 0 (vals c args)

/-- The errno of a call. -/
def errno (σ : State) (mem : List (Nat × Bytes)) (c : Call) (args : List Nat) : Option Nat :=
  (call σ mem c args).2.1

/-- Open `path` (at 512) in fd 3 with oflags `of`, rights `rb`/`ri`, fdflags `ff`; fd cell at 0. -/
def openAt (σ : State) (path : String) (of : Nat := 0) (rb : Nat := 2 ^ 30 - 1 &&& preInh)
    (ri : Nat := preInh) (ff : Nat := 0) (dirfd : Nat := 3) : State × Option Nat × MemInst :=
  call σ [(512, b path)] .pathOpen [dirfd, 1, 512, (b path).length, of, rb, ri, ff, 0]

/-- The descriptor number an open stored. -/
def newFd (r : State × Option Nat × MemInst) : Nat := r.2.2.read 0 4

-- the example world is well formed (T7's start: `State.Wf` is decidable)
example : σ₀.Wf := by decide

-- args/environ: count + Σ(len + 1), NUL-terminated entries (Wf args_sizes_get/args_get;
-- p1:1190–1233)
example : let r := call σ₀ [] .argsSizesGet [0, 4]
    r.2.1 = some 0 ∧ r.2.2.read 0 4 = 2 ∧ r.2.2.read 4 4 = 4 := by decide
example : let r := call σ₀ [] .argsGet [0, 16]
    r.2.1 = some 0 ∧ r.2.2.read 0 4 = 16 ∧ r.2.2.read 4 4 = 18 ∧
      (List.range 4).map (fun i => r.2.2.byte (16 + i)) = b "p" ++ [0] ++ b "x" ++ [0] := by decide
example : let r := call σ₀ [] .environSizesGet [0, 4]
    r.2.1 = some 0 ∧ r.2.2.read 0 4 = 1 ∧ r.2.2.read 4 4 = 4 := by decide
example : let r := call σ₀ [] .environGet [0, 16]
    r.2.1 = some 0 ∧ r.2.2.read 0 4 = 16 ∧
      (List.range 4).map (fun i => r.2.2.byte (16 + i)) = b "K=V" ++ [0] := by decide

-- clock_time_get: E's stated readings (contract); process/thread → badf (p1:1318); id ≥ 4 = out
-- of profile (wasmtime traps converting it: tester-5 C10); a misaligned u64 cell too (witx-docs)
example : let r := call σ₀ [] .clockTimeGet [0, 0, 8]
    r.2.1 = some 0 ∧ r.2.2.read 8 8 = 100 := by decide
example : let r := call σ₀ [] .clockTimeGet [1, 0, 8]
    r.2.1 = some 0 ∧ r.2.2.read 8 8 = 200 := by decide
example : errno σ₀ [] .clockTimeGet [2, 0, 8] = some Errno.badf := by decide
example : errno σ₀ [] .clockTimeGet [3, 0, 8] = some Errno.badf := by decide
example : ok σ₀ [] .clockTimeGet [4, 0, 8] = false := by decide
example : ok σ₀ [] .clockTimeGet [0, 0, 4] = false := by decide
-- W: a monotonic reading may not go back (Wf clock docs); E's reading is admissible
example : ¬ ChoiceOK σ₀ (decode .clockTimeGet (page []) [1, 0, 8]) { time := some 199 } := by
  simp [ChoiceOK, decode, σ₀, State.init]

-- fd_close: absent → badf (p1:1365); a closed preopen is gone (fd_prestat_get → badf)
example : errno σ₀ [] .fdClose [99] = some Errno.badf := by decide
example : let τ := (call σ₀ [] .fdClose [3]).1
    errno τ [] .fdPrestatGet [3, 0] = some Errno.badf ∧ τ.free = [3] := by decide

-- fd_fdstat_get: stdio = type unknown when not a tty, flags 0, rights fd_write (p1:1410–1426);
-- the preopen = directory + the contract's masks; absent → badf
example : let r := call σ₀ [] .fdFdstatGet [1, 0]
    r.2.1 = some 0 ∧ r.2.2.byte 0 = 0 ∧ r.2.2.read 2 2 = 0 ∧ r.2.2.read 8 8 = 64 ∧
      r.2.2.read 16 8 = 64 := by decide
example : let r := call σ₀ [] .fdFdstatGet [3, 0]
    r.2.2.byte 0 = 3 ∧ r.2.2.read 8 8 = preBase ∧ r.2.2.read 16 8 = preInh := by decide
example : errno σ₀ [] .fdFdstatGet [99, 0] = some Errno.badf := by decide
-- padding untouched (field-only writes): byte 1 and bytes 4–7 keep their 0xAA
example : let r := call σ₀ [(0, List.replicate 24 0xAA)] .fdFdstatGet [1, 0]
    r.2.2.byte 1 = 0xAA ∧ r.2.2.read 4 4 = 0xAAAAAAAA := by decide

-- fd_fdstat_set_flags: an unknown bit = out of profile (wasmtime traps: tester-5 C20); stdio →
-- badf (p1:520–526); dsync → inval (p1:1541); append → later writes land at EOF (Wt fdflags)
example : ok σ₀ [] .fdFdstatSetFlags [3, 32] = false := by decide
example : errno σ₀ [] .fdFdstatSetFlags [1, 1] = some Errno.badf := by decide
example : let τ := (openAt σ₀ "f").1
    errno τ [] .fdFdstatSetFlags [4, 2] = some Errno.inval := by decide
example : let τ := (openAt σ₀ "f").1
    let τ' := (call τ [] .fdFdstatSetFlags [4, 1]).1
    (call τ' [(64, b "Z"), (0, iov [(64, 1)])] .fdWrite [4, 0, 1, 40]).1.fileAt (b ".") [b "f"] =
      some (b "abcZ") := by decide

-- fd_prestat_get / fd_prestat_dir_name (p1:1815–1856)
example : let r := call σ₀ [] .fdPrestatGet [3, 0]
    r.2.1 = some 0 ∧ r.2.2.byte 0 = 0 ∧ r.2.2.read 4 4 = 1 := by decide
example : errno σ₀ [] .fdPrestatGet [1, 0] = some Errno.badf := by decide
example : let r := call σ₀ [] .fdPrestatDirName [3, 8, 1]
    r.2.1 = some 0 ∧ r.2.2.byte 8 = 46 := by decide
example : errno σ₀ [] .fdPrestatDirName [3, 8, 0] = some Errno.nametoolong := by decide
example : errno σ₀ [] .fdPrestatDirName [1, 8, 8] = some Errno.notdir := by decide
example : errno σ₀ [] .fdPrestatDirName [99, 8, 8] = some Errno.badf := by decide

-- fd_read: a file in one buffer, then EOF → 0; two buffers → the first only (p1:184–204);
-- empty buffers skipped; stdin: the first non-empty buffer; an empty stdin request → intr
-- (p1:276–287, probe stdin-zero); stdout + directories → badf (p1:1738)
example : let τ := (openAt σ₀ "f").1
    let r := call τ [(0, iov [(64, 10)])] .fdRead [4, 0, 1, 40]
    r.2.1 = some 0 ∧ r.2.2.read 40 4 = 3 ∧
      (List.range 3).map (fun i => r.2.2.byte (64 + i)) = b "abc" ∧
      (call r.1 [(0, iov [(64, 10)])] .fdRead [4, 0, 1, 40]).2.2.read 40 4 = 0 := by decide
example : let τ := (openAt σ₀ "f").1
    let r := call τ [(0, iov [(64, 2), (70, 10)])] .fdRead [4, 0, 2, 40]
    r.2.2.read 40 4 = 2 ∧ r.2.2.byte 64 = 97 ∧ r.2.2.byte 65 = 98 ∧ r.2.2.byte 70 = 0 := by decide
example : let r := call σ₀ [(0, iov [(64, 0), (66, 5)])] .fdRead [0, 0, 2, 40]
    r.2.2.read 40 4 = 2 ∧ r.2.2.byte 66 = 105 ∧ r.2.2.byte 67 = 110 ∧ r.1.stdin = [] := by decide
example : let r := call σ₀ [(0, iov [(64, 0)]), (40, le 4 0x1234)] .fdRead [0, 0, 1, 40]
    r.2.1 = some Errno.intr ∧ r.2.2.read 40 4 = 0x1234 ∧ r.1.stdin = b "in" := by decide
example : errno { σ₀ with stdin := [] } [(0, iov [(64, 1)])] .fdRead [0, 0, 1, 40] = some 0 := by
  decide
example : errno σ₀ [(0, iov [(64, 1)])] .fdRead [1, 0, 1, 40] = some Errno.badf := by decide
example : errno σ₀ [(0, iov [(64, 1)])] .fdRead [3, 0, 1, 40] = some Errno.badf := by decide

-- fd_write: stdout two buffers → `A`, count 1 (consultant-13 probe two_valid_iovecs); a file at
-- its offset; a gap past EOF zero-filled (POSIX pwrite); stdin + directories → badf (p1:711);
-- empty buffers → 0 (probe stdin-zero writezero)
example : let r := call σ₀ [(64, b "AB"), (0, iov [(64, 1), (65, 1)])] .fdWrite [1, 0, 2, 40]
    r.1.stdout = b "A" ∧ r.2.1 = some 0 ∧ r.2.2.read 40 4 = 1 := by decide
example : let τ := (openAt σ₀ "f").1
    let τ₁ := (call τ [(48, le 8 0)] .fdSeek [4, 1, 0, 48]).1
    (call τ₁ [(64, b "Z"), (0, iov [(64, 1)])] .fdWrite [4, 0, 1, 40]).1.fileAt (b ".") [b "f"] =
      some (b "aZc") := by decide
example : let τ := (openAt σ₀ "f").1
    let τ₁ := (call τ [] .fdSeek [4, 5, 0, 48]).1
    (call τ₁ [(64, b "Z"), (0, iov [(64, 1)])] .fdWrite [4, 0, 1, 40]).1.fileAt (b ".") [b "f"] =
      some (b "abc" ++ [0, 0] ++ b "Z") := by decide
example : errno σ₀ [(0, iov [(64, 1)])] .fdWrite [0, 0, 1, 40] = some Errno.badf := by decide
example : errno σ₀ [(0, iov [(64, 1)])] .fdWrite [3, 0, 1, 40] = some Errno.badf := by decide
example : let r := call σ₀ [(0, iov [(64, 0)])] .fdWrite [1, 0, 1, 40]
    r.2.1 = some 0 ∧ r.2.2.read 40 4 = 0 ∧ r.1.stdout = [] := by decide
-- out of profile: a later buffer out of bounds; the count cell inside a buffer; a misaligned cell
example : ok σ₀ [(0, iov [(64, 1), (65536, 1)])] .fdWrite [1, 0, 2, 40] = false := by decide
example : ok σ₀ [(0, iov [(64, 8)])] .fdWrite [1, 0, 1, 64] = false := by decide
example : ok σ₀ [(0, iov [(64, 1)])] .fdWrite [1, 0, 1, 41] = false := by decide
example : ok σ₀ [(0, iov [(64, 1)])] .fdWrite [1, 0, 1, 40] = true := by decide

-- fd_seek (p1:1889–1921; Wt rights: fd_seek implies fd_tell): set/cur/end; set −1 and cur
-- below 0 → inval; whence 3 = out of profile (tester-5 C49); stdio → spipe (p1:538–543);
-- directory/absent → badf
example : let τ := (openAt σ₀ "f").1
    let r₁ := call τ [] .fdSeek [4, 2, 0, 48]
    let r₂ := call r₁.1 [] .fdSeek [4, 2 ^ 64 - 1, 1, 48]
    let r₃ := call r₂.1 [] .fdSeek [4, 0, 2, 48]
    r₁.2.2.read 48 8 = 2 ∧ r₂.2.2.read 48 8 = 1 ∧ r₃.2.2.read 48 8 = 3 := by decide
example : let τ := (openAt σ₀ "f").1
    errno τ [] .fdSeek [4, 2 ^ 64 - 1, 0, 48] = some Errno.inval ∧
      errno τ [] .fdSeek [4, 2 ^ 64 - 1, 1, 48] = some Errno.inval ∧
      ok τ [] .fdSeek [4, 0, 3, 48] = false := by decide
example : errno σ₀ [] .fdSeek [1, 0, 1, 48] = some Errno.spipe := by decide
example : errno σ₀ [] .fdSeek [3, 0, 1, 48] = some Errno.badf := by decide
example : errno σ₀ [] .fdSeek [99, 0, 1, 48] = some Errno.badf := by decide
-- tell-only rights: (0, cur) allowed, any other seek → notcapable
example : let τ := (openAt σ₀ "f" (rb := 2 ^ Right.fdTell)).1
    errno τ [] .fdSeek [4, 0, 1, 48] = some 0 ∧
      errno τ [] .fdSeek [4, 1, 0, 48] = some Errno.notcapable := by decide

-- path_open: E's fd = max open + 1 (p1:440–465); libc O_WRONLY|O_CREAT|O_TRUNC rights on the
-- initial preopen (wasi-libc openat: max ∩ the dirfd's inheriting) succeed (contract masks)
example : let r := openAt σ₀ "f"
    r.2.1 = some 0 ∧ newFd r = 4 := by decide
example : let libc := (2 ^ 64 - 1 - rights [0, 1, 6, 8, 14, 22]) ||| rights [0, 6, 8, 22]
    let r := openAt σ₀ "f" (of := Oflags.creat ||| Oflags.trunc) (rb := libc &&& preInh)
    r.2.1 = some 0 ∧ r.1.fileAt (b ".") [b "f"] = some [] := by decide
example : let r := openAt σ₀ "new" (of := Oflags.creat)
    r.2.1 = some 0 ∧ r.1.fileAt (b ".") [b "new"] = some [] := by decide
example : (openAt σ₀ "f" (of := Oflags.creat ||| Oflags.excl)).2.1 = some Errno.exist := by
  decide
-- excl without creat ignored (probe c13 paths: excl alone on an existing file → 0)
example : (openAt σ₀ "f" (of := Oflags.excl)).2.1 = some 0 := by decide
-- directory flag or a trailing slash on a file → notdir; "new/" with creat → isdir, no file
-- (probe c13 paths); a directory with fd_write requested → isdir; read-only → a dir fd
example : (openAt σ₀ "f" (of := Oflags.directory)).2.1 = some Errno.notdir := by decide
example : (openAt σ₀ "f/").2.1 = some Errno.notdir := by decide
example : let r := openAt σ₀ "new/" (of := Oflags.creat)
    r.2.1 = some Errno.isdir ∧ r.1.fileAt (b ".") [b "new"] = none := by decide
example : (openAt σ₀ "d").2.1 = some Errno.isdir := by decide
example : (openAt σ₀ "d" (rb := 2 ^ Right.fdRead)).2.1 = some 0 := by decide
example : (openAt σ₀ "x" (of := Oflags.directory ||| Oflags.creat)).2.1 = some Errno.inval := by
  decide
-- walk errors: missing → noent; missing intermediate → noent; intermediate file → notdir;
-- `f/..` → notdir (typed walk, probe c13); escape + absolute → perm; empty → noent; NUL → inval
example : (openAt σ₀ "nope").2.1 = some Errno.noent := by decide
example : (openAt σ₀ "nope/f").2.1 = some Errno.noent := by decide
example : (openAt σ₀ "f/x").2.1 = some Errno.notdir := by decide
example : (openAt σ₀ "f/..").2.1 = some Errno.notdir := by decide
example : (openAt σ₀ "../f").2.1 = some Errno.perm := by decide
example : (openAt σ₀ "/f").2.1 = some Errno.perm := by decide
example : (openAt σ₀ "").2.1 = some Errno.noent := by decide
example : (call σ₀ [(512, b "f" ++ [0])] .pathOpen [3, 1, 512, 2, 0, 2, 0, 0, 0]).2.1 =
    some Errno.inval := by decide
example : (openAt σ₀ "d/../f" (rb := 2 ^ Right.fdRead)).2.1 = some 0 := by decide
example : (openAt σ₀ "d/g/../f").2.1 = some Errno.notdir := by decide
-- dirfd: a file → notdir (p1:2189); stdout → badf (p1:2190); an unknown oflags bit = out of
-- profile (tester-5 C76)
example : let τ := (openAt σ₀ "f").1
    (openAt τ "f" (dirfd := 4)).2.1 = some Errno.notdir := by decide
example : (openAt σ₀ "f" (dirfd := 1)).2.1 = some Errno.badf := by decide
example : ok σ₀ [(512, b "f")] .pathOpen [3, 1, 512, 1, 16, preInh, preInh, 0, 0] = false := by
  decide
-- rights beyond the dirfd's inheriting set → notcapable (WITX rights; contract)
example : (openAt σ₀ "f" (rb := 2 ^ 29)).2.1 = some Errno.notcapable := by decide
-- fd reuse = the greatest freed fd (probe fd-reuse: 4, 5, 6; close 4 + 6 → 6, then 4)
example : let r₄ := openAt σ₀ "f"
    let r₅ := openAt r₄.1 "f"
    let r₆ := openAt r₅.1 "f"
    let τ := (call (call r₆.1 [] .fdClose [4]).1 [] .fdClose [6]).1
    let a := openAt τ "f"
    [newFd r₄, newFd r₅, newFd r₆, newFd a, newFd (openAt a.1 "f")] = [4, 5, 6, 6, 4] := by decide
-- two opens of one file keep their own offsets (Wt: an offset per descriptor)
example : let τ := (openAt (openAt σ₀ "f").1 "f").1
    let r := call τ [(0, iov [(64, 2)])] .fdRead [4, 0, 1, 40]
    let r' := call r.1 [(0, iov [(64, 1)])] .fdRead [5, 0, 1, 40]
    r'.2.2.byte 64 = 97 := by decide

-- path_create_directory (+ trailing slash, probe c13), path_remove_directory, path_unlink_file
example : let r := call σ₀ [(512, b "n")] .pathCreateDirectory [3, 512, 1]
    r.2.1 = some 0 ∧ ((r.1.walkNames 0 [b "n"]).map r.1.isDir) = some true := by decide
example : errno σ₀ [(512, b "d")] .pathCreateDirectory [3, 512, 1] = some Errno.exist := by decide
example : errno σ₀ [(512, b "n/")] .pathCreateDirectory [3, 512, 2] = some 0 := by decide
example : errno σ₀ [(512, b "z/n")] .pathCreateDirectory [3, 512, 3] = some Errno.noent := by
  decide
example : let τ := (openAt σ₀ "f").1
    errno τ [(512, b "n")] .pathCreateDirectory [4, 512, 1] = some Errno.badf := by decide
example : errno σ₀ [(512, b "e")] .pathRemoveDirectory [3, 512, 1] = some 0 := by decide
example : errno σ₀ [(512, b "d")] .pathRemoveDirectory [3, 512, 1] = some Errno.notempty := by
  decide
example : errno σ₀ [(512, b "f")] .pathRemoveDirectory [3, 512, 1] = some Errno.notdir := by
  decide
example : errno σ₀ [(512, b "z")] .pathRemoveDirectory [3, 512, 1] = some Errno.noent := by decide
example : errno σ₀ [(512, b "d/.")] .pathRemoveDirectory [3, 512, 3] = some Errno.inval := by
  decide
example : errno σ₀ [(512, b "d/..")] .pathRemoveDirectory [3, 512, 4] = some Errno.inval := by
  decide
example : errno σ₀ [(512, b "f")] .pathUnlinkFile [3, 512, 1] = some 0 := by decide
example : errno σ₀ [(512, b "d")] .pathUnlinkFile [3, 512, 1] = some Errno.isdir := by decide
example : errno σ₀ [(512, b "d/")] .pathUnlinkFile [3, 512, 2] = some Errno.isdir := by decide
example : errno σ₀ [(512, b "f/")] .pathUnlinkFile [3, 512, 2] = some Errno.notdir := by decide
example : errno σ₀ [(512, b "z")] .pathUnlinkFile [3, 512, 1] = some Errno.noent := by decide
-- unlink while open: the open fd still reads the old data; a recreated `f` is a new empty file
example : let τ := (openAt σ₀ "f").1
    let τ₁ := (call τ [(512, b "f")] .pathUnlinkFile [3, 512, 1]).1
    let τ₂ := (openAt τ₁ "f" (of := Oflags.creat)).1
    let r := call τ₂ [(0, iov [(64, 3)])] .fdRead [4, 0, 1, 40]
    r.2.2.read 40 4 = 3 ∧ r.2.2.byte 64 = 97 ∧ τ₂.fileAt (b ".") [b "f"] = some [] := by decide

-- path_filestat_get: dev 1 (p1:2088), ino = node + 1, type, nlink 1, size, times 0 (contract);
-- a directory's size 0 (contract); missing → noent; `f/` → notdir; lookupflags bit 1 = out of
-- profile (tester-5 C101)
example : let r := call σ₀ [(512, b "f")] .pathFilestatGet [3, 1, 512, 1, 64]
    r.2.1 = some 0 ∧ r.2.2.read 64 8 = 1 ∧ r.2.2.read 72 8 = 2 ∧ r.2.2.byte 80 = 4 ∧
      r.2.2.read 88 8 = 1 ∧ r.2.2.read 96 8 = 3 ∧ r.2.2.read 104 8 = 0 := by decide
example : let r := call σ₀ [(512, b "d")] .pathFilestatGet [3, 1, 512, 1, 64]
    r.2.2.byte 80 = 3 ∧ r.2.2.read 96 8 = 0 ∧ r.2.2.read 72 8 = 3 := by decide
example : errno σ₀ [(512, b "z")] .pathFilestatGet [3, 1, 512, 1, 64] = some Errno.noent := by
  decide
example : errno σ₀ [(512, b "f/")] .pathFilestatGet [3, 1, 512, 2, 64] = some Errno.notdir := by
  decide
example : ok σ₀ [(512, b "f")] .pathFilestatGet [3, 2, 512, 1, 64] = false := by decide
-- serial numbers: distinct for two new files, stable across queries
example : let τ := (openAt (openAt σ₀ "n1" (of := Oflags.creat)).1 "n2" (of := Oflags.creat)).1
    let i₁ := (call τ [(512, b "n1")] .pathFilestatGet [3, 1, 512, 2, 64]).2.2.read 72 8
    let i₂ := (call τ [(512, b "n2")] .pathFilestatGet [3, 1, 512, 2, 64]).2.2.read 72 8
    i₁ = 6 ∧ i₂ = 7 := by decide

-- W: an injected failure returns its errno and changes neither the world nor the memory
example : let ch : Choice := { err := some Errno.perm }
    let r := call σ₀ [(64, b "AB"), (0, iov [(64, 2)])] .fdWrite [1, 0, 1, 40] ch
    r.1.stdout = [] ∧ r.2.1 = some Errno.perm ∧ r.2.2.read 40 4 = 0 := by decide

-- proc_exit: the exit status in the world, a trap carrier (System layer)
example : let r := call σ₀ [] .procExit [3]
    r.1.exited = some 3 ∧ r.2.1 = none := by decide

-- random_get: E's bytes = the choice, cut or zero-padded to the buffer
example : let r := call σ₀ [] .randomGet [64, 2] { bytes := [7, 9, 11] }
    r.2.1 = some 0 ∧ r.2.2.byte 64 = 7 ∧ r.2.2.byte 65 = 9 ∧ r.2.2.byte 66 = 0 := by decide

-- every 2-byte string is a `random_get` output (Wf random_get fills the buffer)
example (b₀ b₁ : UInt8) : let r := call σ₀ [] .randomGet [64, 2] { bytes := [b₀, b₁] }
    r.2.2.byte 64 = b₀ ∧ r.2.2.byte 65 = b₁ := by
  simp [call, exec, step, FVA.Wasi.run, decode, Examples.vals, Call.args, Call.info, writeBytes,
    page, Store.setMem]

-- spawn: the next process reads the whole stdout, sees the files, starts at fd 4 again
example : let τ := (call σ₀ [(64, b "hi"), (0, iov [(64, 2)])] .fdWrite [1, 0, 1, 40]).1
    let τ' := (openAt τ "new" (of := Oflags.creat)).1.spawn [b "q"]
    τ'.stdin = b "hi" ∧ τ'.stdout = [] ∧ τ'.fileAt (b ".") [b "new"] = some [] ∧
      newFd (openAt τ' "f") = 4 := by decide


/-! ## Boundaries (reviewer-5 R2 R5 R7 R11 R12 R13 R20, MAIN L1h; probes `FVATest/Wasi/probes/`) -/

/-- In the profile on a 4 GiB (65,536-page) memory? -/
def bigOk (c : Call) (args : List Nat) : Bool :=
  inProfile σ₀ c { mems := [⟨65536, none, fun _ => 0⟩] } 0 (vals c args)

-- a buffer ending at 2^32 lies outside the profile (wasmtime traps on the pointer past it:
-- p1:1171,1177,1249; probe `MemoryEnd`); one byte earlier is inside
example : bigOk .environGet [0, 2 ^ 32 - 4] = false ∧ bigOk .environGet [0, 2 ^ 32 - 5] = true := by
  decide
example : bigOk .fdPrestatDirName [3, 2 ^ 32 - 1, 1] = false ∧
    bigOk .fdPrestatDirName [3, 2 ^ 32 - 2, 1] = true := by decide
example : bigOk .randomGet [2 ^ 32 - 1, 1] = false ∧ bigOk .randomGet [2 ^ 32 - 2, 1] = true := by
  decide

-- a directory keeps no fdflags (p1:1472; probe `OpenFlags`: fdstat flags 0)
example : ∀ ff ∈ [Fdflags.append, Fdflags.nonblock],
    let r := openAt σ₀ "d" (rb := rights [Right.fdRead]) (ri := 0) (ff := ff)
    r.2.1 = some 0 ∧ (call r.1 [] .fdFdstatGet [newFd r, 64]).2.2.read 66 2 = 0 := by decide

-- sync fdflags → notsup, on files and directories (probe `OpenFlags`: 58)
example : ∀ ff ∈ [Fdflags.dsync, Fdflags.rsync, Fdflags.sync],
    (openAt σ₀ "f" (ff := ff)).2.1 = some Errno.notsup := by decide
example : (openAt σ₀ "d" (rb := rights [Right.fdRead]) (ri := 0) (ff := Fdflags.sync)).2.1 =
    some Errno.notsup := by decide

-- E at the off_t limit: a positioned transfer reaching 2^63 → inval (Linux rw_verify_area;
-- probes `OffsetIO`, `Append` 3 3 1); empty transfers below it succeed
example : let τ := (call (openAt σ₀ "f").1 [] .fdSeek [4, 2 ^ 63 - 1, 0, 48]).1
    errno τ [(0, iov [(64, 1)])] .fdRead [4, 0, 1, 40] = some Errno.inval ∧
    errno τ [(0, iov [(64, 0)])] .fdRead [4, 0, 1, 40] = some 0 ∧
    errno τ [(0, iov [(64, 0)])] .fdWrite [4, 0, 1, 40] = some 0 := by decide
example : let τ := (call (call (openAt σ₀ "f").1 [] .fdSeek [4, 2 ^ 63 - 1, 0, 48]).1 []
      .fdSeek [4, 1, 1, 48]).1
    errno τ [(0, iov [(64, 0)])] .fdRead [4, 0, 1, 40] = some Errno.inval ∧
    errno τ [(0, iov [(64, 0)])] .fdWrite [4, 0, 1, 40] = some Errno.inval := by decide
example : let τ := (call (openAt σ₀ "f").1 [] .fdSeek [4, 2 ^ 63 - 3, 0, 48]).1
    errno τ [(64, b "XYZ"), (0, iov [(64, 3)])] .fdWrite [4, 0, 1, 40] = some Errno.inval := by
  decide

/-- File 1 = `n` zero bytes, fd 4 appending (a 2^63-byte file has no literal: `simp`). -/
def σApp (n : Nat) : State :=
  { args := [], env := [], stdin := [], stdout := [], stderr := [],
    fds := [(4, ⟨.file 1 0, Fdflags.append, rights [Right.fdWrite], 0⟩)], free := [],
    nodes := [⟨1, .dir [(b "f", 1)]⟩, ⟨2, .file (List.replicate n 0)⟩], roots := [(b ".", 0)],
    clocks := [0, 0, 0, 0], dev := 1, exited := none }

-- E's appends at the file-size limit (Linux generic_write_check_limits on tmpfs; probe `Append`):
-- from `fileMax` → fbig; an empty one succeeds; below it the write is cut at `fileMax`
example (n : Nat) (hn : fileMax ≤ n) :
    run (σApp n) ⟨.fdWrite, [4, 0, 1, 32], [(64, 1)], [[65]], []⟩ {} = .error Errno.fbig := by
  simp (config := { decide := true }) [run, σApp, State.desc, State.data, Fdflags.append, hn]
example (n : Nat) : ∃ τ,
    run (σApp n) ⟨.fdWrite, [4, 0, 1, 32], [(64, 0)], [[]], []⟩ {} = .ok (τ, [(32, le 4 0)]) := by
  simp (config := { decide := true }) [run, σApp, State.desc, State.data, firstLen,
    Fdflags.append]
example (n : Nat) (hn : n + 4 = fileMax) : ∃ τ,
    run (σApp n) ⟨.fdWrite, [4, 0, 1, 32], [(64, 10)], [List.replicate 10 65], []⟩ {} =
      .ok (τ, [(32, le 4 4)]) ∧ (τ.data 1).length = fileMax := by
  have h4 : fileMax - n = 4 := by omega
  have hlt : ¬ fileMax ≤ n := by omega
  simp (config := { decide := true }) [run, σApp, State.desc, State.data, State.setBody,
    State.setDesc, firstLen, Fdflags.append, h4, hlt]
  omega

-- no new entries in a removed directory (POSIX rmdir; probe `UnlinkedDirectory`: 44, 44)
example : let r := openAt σ₀ "e" (rb := rights [Right.pathOpen, Right.pathCreateFile,
      Right.pathCreateDirectory]) (ri := rights [Right.fdRead, Right.fdWrite])
    let τ := (call r.1 [(512, b "e")] .pathRemoveDirectory [3, 512, 1]).1
    r.2.1 = some 0 ∧ newFd r = 4 ∧
      errno τ [(512, b "child")] .pathOpen [4, 0, 512, 5, Oflags.creat, 0, 0, 0, 0] =
        some Errno.noent ∧
      errno τ [(512, b "hild")] .pathCreateDirectory [4, 512, 4] = some Errno.noent := by decide

-- serial numbers are u64 (typenames.witx:332–333): 2^64 + 2 is no W choice; E's run out at 2^64
example : ¬ ChoiceOK σ₀ (decode .pathOpen (page [(512, b "new")]) [3, 0, 512, 3, 1, 66, 0, 0, 0])
    { ino := some (2 ^ 64 + 2) } := by
  intro h; exact absurd (h.2.2.2.2.1 _ rfl).1 (by decide)
example : (openAt { σ₀ with nodes := σ₀.nodes.set 4 ⟨2 ^ 64 - 1, .dir []⟩ } "new"
    (of := Oflags.creat)).2.1 = some Errno.nospc := by decide

-- errno branches the matrix lacked (R20): args/environ overflow (p1:1223–1229; a 2^32-byte
-- argument has no literal: `simp`), no descriptor number left (Wf path_open: fd < 2^31), missing
-- fd_read / fd_write rights on files and streams (typenames.witx rights)
example (n : Nat) (hn : 2 ^ 32 ≤ n) : run { σ₀ with args := [List.replicate n 65] }
    (decode .argsSizesGet (page []) [0, 4]) {} = .error Errno.overflow := by
  simp [run, run.sizes, decode]
  omega
example (n : Nat) (hn : 2 ^ 32 ≤ n) : run { σ₀ with env := [List.replicate n 65] }
    (decode .environSizesGet (page []) [0, 4]) {} = .error Errno.overflow := by
  simp [run, run.sizes, decode]
  omega
example : (openAt { σ₀ with free := [2 ^ 31] } "f").2.1 = some Errno.mfile := by decide
example : errno (openAt σ₀ "f" (rb := rights [Right.fdWrite])).1 [(0, iov [(64, 1)])] .fdRead
      [4, 0, 1, 40] = some Errno.notcapable ∧
    errno (openAt σ₀ "f" (rb := rights [Right.fdRead])).1 [(64, b "Z"), (0, iov [(64, 1)])]
      .fdWrite [4, 0, 1, 40] = some Errno.notcapable := by decide
example : errno { σ₀ with fds := (0, ⟨.stream 0 Filetype.unknown, 0, 0, 0⟩) :: σ₀.fds }
      [(0, iov [(64, 1)])] .fdRead [0, 0, 1, 40] = some Errno.notcapable ∧
    errno { σ₀ with fds := (1, ⟨.stream 1 Filetype.unknown, 0, 0, 0⟩) :: σ₀.fds }
      [(64, b "Z"), (0, iov [(64, 1)])] .fdWrite [1, 0, 1, 40] = some Errno.notcapable := by
  decide

-- per-call wiring of the shared path checks (R20 branch audit): the call's own right, a
-- non-directory fd, an absolute path, a NUL, an intermediate file, E's serial exhaustion
example : let τ := (openAt σ₀ "d" (rb := rights [Right.pathOpen]) (ri := 0)).1
    errno τ [(512, b "x")] .pathCreateDirectory [4, 512, 1] = some Errno.notcapable ∧
    errno τ [(512, b "g")] .pathRemoveDirectory [4, 512, 1] = some Errno.notcapable ∧
    errno τ [(512, b "g")] .pathUnlinkFile [4, 512, 1] = some Errno.notcapable ∧
    errno τ [(512, b "g")] .pathFilestatGet [4, 0, 512, 1, 64] = some Errno.notcapable := by
  decide
example : ∀ c ∈ [Call.pathCreateDirectory, .pathRemoveDirectory, .pathUnlinkFile],
    errno σ₀ [(512, b "/x")] c [3, 512, 2] = some Errno.perm ∧
      errno σ₀ [(512, [120, 0])] c [3, 512, 2] = some Errno.inval ∧
      errno σ₀ [(512, b "x")] c [1, 512, 1] = some Errno.badf := by decide
example : errno σ₀ [(512, b "/x")] .pathFilestatGet [3, 0, 512, 2, 64] = some Errno.perm ∧
    errno σ₀ [(512, [120, 0])] .pathFilestatGet [3, 0, 512, 2, 64] = some Errno.inval ∧
    errno σ₀ [(512, b "x")] .pathFilestatGet [1, 0, 512, 1, 64] = some Errno.badf := by decide
example : errno σ₀ [(512, b "f/x")] .pathCreateDirectory [3, 512, 3] = some Errno.notdir ∧
    errno { σ₀ with nodes := σ₀.nodes.set 4 ⟨2 ^ 64 - 1, .dir []⟩ } [(512, b "n")]
      .pathCreateDirectory [3, 512, 1] = some Errno.nospc := by decide
example : errno (openAt σ₀ "f" (rb := rights [Right.fdWrite])).1 [] .fdFdstatSetFlags [4, 1] =
    some Errno.notcapable := by decide

end FVA.Wasi.Examples
