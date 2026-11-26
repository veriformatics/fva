import FVA.Spec.Wasi.State
import FVA.Spec.Exec.Step

/-!
# The 20 declared WASI preview1 calls (reviewed spec)

One semantics for each call, in three layers: `decode` reads a call's inputs from the guest's
memory, `step` moves the world (memory-free: it returns the bytes to store and where), `exec`
stores them and gives the host outcome. Every nondeterministic choice WITX leaves to the host is
an explicit `Choice` field; `none` = the environment `E`'s choice (wasmtime 50.0.0's policy where
it lies inside WITX, else a named completion; `docs/contracts/U29a-wasi.md`). Each error code
cites its source: WITX where it names one, else wasmtime 50.0.0 `crates/wasi/src/p1.rs` (`p1:`).

`exec` assumes the profile domain `inProfile`: every pointer the call may dereference aligned + in
bounds below the 32-bit address-space end, the regions it writes apart from each other and from the
ones it reads, sub-32-bit scalars within their WITX width. Outside it the world relation
(`FVA.Spec.Wasi.World`) allows any typed outcome: hosts trap there at different points, after
different effects. Two host assumptions beyond WITX hold in every outcome: a structure result stores
its fields alone (its padding keeps its bytes, as wasmtime's wiggle does) and a failed call has no
effect.
-/

namespace FVA.Wasi

open FVA.Wasm FVA.Wasm.Exec

/-- The declared calls (Decisions: WASI). -/
inductive Call where
  | argsGet | argsSizesGet | environGet | environSizesGet | clockTimeGet | fdClose
  | fdFdstatGet | fdFdstatSetFlags | fdPrestatGet | fdPrestatDirName | fdRead | fdSeek
  | fdWrite | pathCreateDirectory | pathFilestatGet | pathOpen | pathRemoveDirectory
  | pathUnlinkFile | procExit | randomGet
  deriving DecidableEq

/-- The WITX name and the raw wasm32 parameters (`true` = `i64`) of each call. -/
def Call.info : Call → String × List Bool
  | .argsGet => ("args_get", [false, false])
  | .argsSizesGet => ("args_sizes_get", [false, false])
  | .environGet => ("environ_get", [false, false])
  | .environSizesGet => ("environ_sizes_get", [false, false])
  | .clockTimeGet => ("clock_time_get", [false, true, false])
  | .fdClose => ("fd_close", [false])
  | .fdFdstatGet => ("fd_fdstat_get", [false, false])
  | .fdFdstatSetFlags => ("fd_fdstat_set_flags", [false, false])
  | .fdPrestatGet => ("fd_prestat_get", [false, false])
  | .fdPrestatDirName => ("fd_prestat_dir_name", [false, false, false])
  | .fdRead => ("fd_read", [false, false, false, false])
  | .fdSeek => ("fd_seek", [false, true, false, false])
  | .fdWrite => ("fd_write", [false, false, false, false])
  | .pathCreateDirectory => ("path_create_directory", [false, false, false])
  | .pathFilestatGet => ("path_filestat_get", [false, false, false, false, false])
  | .pathOpen => ("path_open", [false, false, false, false, false, true, true, false, false])
  | .pathRemoveDirectory => ("path_remove_directory", [false, false, false])
  | .pathUnlinkFile => ("path_unlink_file", [false, false, false])
  | .procExit => ("proc_exit", [false])
  | .randomGet => ("random_get", [false, false])

/-- Every declared call. -/
def Call.all : List Call :=
  [.argsGet, .argsSizesGet, .environGet, .environSizesGet, .clockTimeGet, .fdClose, .fdFdstatGet,
   .fdFdstatSetFlags, .fdPrestatGet, .fdPrestatDirName, .fdRead, .fdSeek, .fdWrite,
   .pathCreateDirectory, .pathFilestatGet, .pathOpen, .pathRemoveDirectory, .pathUnlinkFile,
   .procExit, .randomGet]

/-- The call a `wasi_snapshot_preview1` import name names. -/
def Call.ofName (n : String) : Option Call := Call.all.find? (·.info.1 = n)

/-- The call's raw wasm32 signature; every call but `proc_exit` returns its errno as an `i32`. -/
def Call.sig (c : Call) : FuncType :=
  ⟨c.info.2.map fun w => .num (if w then .i64 else .i32),
   if c = .procExit then [] else [.num .i32]⟩

/-- The arguments as unsigned numbers, if `vs` has the call's parameter types. -/
def Call.args (c : Call) (vs : List Val) : Option (List Nat) :=
  if vs.length = c.info.2.length then
    (vs.zip c.info.2).mapM fun
      | (.i32 v, false) => some v.toNat
      | (.i64 v, true) => some v.toNat
      | _ => none
  else none

/-- The `k` little-endian bytes of `v`. -/
def le (k v : Nat) : Bytes := (List.range k).map fun i => UInt8.ofNat (v / 256 ^ i)

/-- The `n` bytes of `m` from `a`. -/
def memBytes (m : MemInst) (a n : Nat) : Bytes := (List.range n).map fun i => m.byte (a + i)

/-- `m` with `bs` stored from `a`. -/
def writeBytes (m : MemInst) (a : Nat) (bs : Bytes) : MemInst :=
  { m with byte := fun x => if a ≤ x ∧ x < a + bs.length then bs.getD (x - a) 0 else m.byte x }

/-- The `n` (address, length) pairs of the iovec array at `p` (8 bytes each: u32 address, u32
length). -/
def iovecs (m : MemInst) (p n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun i => (m.read (p + 8 * i) 4, m.read (p + 8 * i + 4) 4)

/-- A memory region a call may access: start, length, alignment, written or only read. -/
structure Region where
  /-- First byte. -/
  addr : Nat
  /-- Length in bytes. -/
  len : Nat
  /-- The pointee's alignment. -/
  align : Nat
  /-- Written (else only read). -/
  write : Bool

/-- The regions call `c` may access with arguments `a` (maximal reading: every listed iovec
buffer, the whole `fd_prestat_dir_name` buffer; pointee alignments of wasi-libc's `wasip1.h`). -/
def Call.regions (c : Call) (σ : State) (m : MemInst) (a : List Nat) : List Region :=
  let x := a.getD
  let entries (es : List Bytes) : List Region :=
    [⟨x 0 0, 4 * es.length, 4, true⟩, ⟨x 1 0, (es.map (·.length + 1)).sum, 1, true⟩]
  let bufs (w : Bool) : List Region := (iovecs m (x 1 0) (x 2 0)).map fun b => ⟨b.1, b.2, 1, w⟩
  match c with
  | .argsGet => entries σ.args
  | .environGet => entries σ.env
  | .argsSizesGet | .environSizesGet => [⟨x 0 0, 4, 4, true⟩, ⟨x 1 0, 4, 4, true⟩]
  | .clockTimeGet => [⟨x 2 0, 8, 8, true⟩]
  | .fdFdstatGet => [⟨x 1 0, 24, 8, true⟩]
  | .fdPrestatGet => [⟨x 1 0, 8, 4, true⟩]
  | .fdPrestatDirName => [⟨x 1 0, x 2 0, 1, true⟩]
  | .fdRead => ⟨x 1 0, 8 * x 2 0, 4, false⟩ :: bufs true ++ [⟨x 3 0, 4, 4, true⟩]
  | .fdWrite => ⟨x 1 0, 8 * x 2 0, 4, false⟩ :: bufs false ++ [⟨x 3 0, 4, 4, true⟩]
  | .fdSeek => [⟨x 3 0, 8, 8, true⟩]
  | .pathCreateDirectory | .pathRemoveDirectory | .pathUnlinkFile => [⟨x 1 0, x 2 0, 1, false⟩]
  | .pathFilestatGet => [⟨x 2 0, x 3 0, 1, false⟩, ⟨x 4 0, 64, 8, true⟩]
  | .pathOpen => [⟨x 2 0, x 3 0, 1, false⟩, ⟨x 8 0, 4, 4, true⟩]
  | .randomGet => [⟨x 0 0, x 1 0, 1, true⟩]
  | .fdClose | .fdFdstatSetFlags | .procExit => []

/-- Scalar arguments hold valid WITX values (wasmtime traps at their conversion otherwise:
tester-5's probes): clock id < 4, `whence` < 3, `fdflags` < 32, `oflags` < 16, `lookupflags` < 2,
rights below bit 30. -/
def Call.valuesOk (c : Call) (a : List Nat) : Bool :=
  let x := a.getD
  match c with
  | .clockTimeGet => x 0 0 < clockCount
  | .fdSeek => x 2 0 < 3
  | .fdFdstatSetFlags => x 1 0 < 32
  | .pathOpen => x 1 0 < 2 && x 4 0 < 16 && x 5 0 < 2 ^ Right.count &&
      x 6 0 < 2 ^ Right.count && x 7 0 < 32
  | .pathFilestatGet => x 1 0 < 2
  | _ => true

/-- Two regions share no byte. -/
def Region.apart (r q : Region) : Bool :=
  r.len == 0 || q.len == 0 || r.addr + r.len ≤ q.addr || q.addr + q.len ≤ r.addr

/-- The profile domain: typed arguments with valid scalar values, every region aligned + inside
memory `mem` + ending below 2^32 (wasmtime 50.0.0 traps on a buffer ending at 2^32: the pointer
past its last byte overflows, p1:1171,1177,1203,1249; probe r5 `MemoryEnd`), every written region
apart from every other region. -/
def inProfile (σ : State) (c : Call) (s : Store) (mem : Nat) (vs : List Val) : Bool :=
  match s.mems[mem]?, c.args vs with
  | some m, some a =>
    let rs := c.regions σ m a
    c.valuesOk a &&
      rs.all (fun r => r.addr % r.align == 0 && r.addr + r.len ≤ m.size &&
        r.addr + r.len < 2 ^ 32) &&
      (List.range rs.length).all fun i => (List.range rs.length).all fun j =>
        i == j || !(rs.getD i ⟨0, 0, 1, false⟩).write ||
          (rs.getD i ⟨0, 0, 1, false⟩).apart (rs.getD j ⟨0, 0, 1, false⟩)
  | _, _ => false

/-- A decoded call: the arguments, the iovecs of `fd_read`/`fd_write`, the bytes of each
`fd_write` buffer, the path of a path call. -/
structure Req where
  /-- The call. -/
  call : Call
  /-- Its raw arguments, unsigned. -/
  args : List Nat
  /-- `fd_read`/`fd_write`'s iovecs (address, length). -/
  iovs : List (Nat × Nat)
  /-- `fd_write`'s bytes, one list per buffer. -/
  data : List Bytes
  /-- A path call's path bytes. -/
  path : Bytes

/-- The inputs of call `c` with arguments `a`, read from memory `m`. -/
def decode (c : Call) (m : MemInst) (a : List Nat) : Req :=
  let iovs := if c = .fdRead ∨ c = .fdWrite then iovecs m (a.getD 1 0) (a.getD 2 0) else []
  { call := c
    args := a
    iovs := iovs
    data := if c = .fdWrite then iovs.map fun b => memBytes m b.1 b.2 else []
    path := match c with
      | .pathCreateDirectory | .pathRemoveDirectory | .pathUnlinkFile =>
        memBytes m (a.getD 1 0) (a.getD 2 0)
      | .pathFilestatGet | .pathOpen => memBytes m (a.getD 2 0) (a.getD 3 0)
      | _ => [] }

/-- The `filestat` fields WITX leaves to the host (W abstracts link counts, directory sizes and
timestamp history). -/
structure StatChoice where
  /-- Link count. -/
  nlink : Nat
  /-- A directory's size. -/
  size : Nat
  /-- Last access time. -/
  atim : Nat
  /-- Last modification time. -/
  mtim : Nat
  /-- Last status change time. -/
  ctim : Nat

/-- A host's choices for one call; `none` = `E`'s choice. -/
structure Choice where
  /-- A failure with no effect. -/
  err : Option Nat := none
  /-- Bytes transferred. -/
  count : Option Nat := none
  /-- A new descriptor's number. -/
  fd : Option Nat := none
  /-- A clock reading. -/
  time : Option Nat := none
  /-- A new node's serial number. -/
  ino : Option Nat := none
  /-- A new descriptor's rights (WITX lets a host drop the ones that do not apply to the file
  type). -/
  rights : Option (Nat × Nat) := none
  /-- `filestat`'s free fields. -/
  stat : Option StatChoice := none
  /-- `random_get`'s output (padded with zeros or cut to the buffer). -/
  bytes : Bytes := []

/-- A call's result: the bytes to store (address, bytes), an error code (no effect), or the
process's exit. -/
inductive Resp where
  | ok (writes : List (Nat × Bytes))
  | err (e : Nat)
  | exit (k : Nat)

/-- Bytes a stdin read returns at most (wasmtime 50.0.0: 1 MiB redirected or piped → 65,536;
`FVATest/Wasi/probes/stdin-chunk.wat`). -/
def stdinChunk : Nat := 65536

/-- `E`'s largest file size (POSIX `off_t` max; a named completion: WITX sizes are u64). -/
def fileMax : Nat := 2 ^ 63 - 1

namespace State

/-- Descriptor `fd`. -/
def desc (σ : State) (fd : Nat) : Option Desc := σ.fds.lookup fd

/-- `σ` with descriptor `fd` replaced by `d`. -/
def setDesc (σ : State) (fd : Nat) (d : Desc) : State :=
  { σ with fds := σ.fds.map fun e => if e.1 = fd then (fd, d) else e }

/-- The contents of node `n` (empty for a directory). -/
def data (σ : State) (n : Nat) : Bytes :=
  match σ.nodes[n]? with
  | some ⟨_, .file d⟩ => d
  | _ => []

/-- `σ` with node `n`'s body replaced by `b`. -/
def setBody (σ : State) (n : Nat) (b : Body) : State :=
  { σ with nodes := σ.nodes.mapIdx fun i nd => if i = n then { nd with body := b } else nd }

/-- `E`'s number for a new descriptor (wasmtime 50.0.0: the greatest closed one, else one past
the greatest open one; p1:440–465). -/
def nextFd (σ : State) : Nat :=
  σ.free.max?.getD ((σ.fds.map (·.1)).max?.map (· + 1) |>.getD 0)

/-- `E`'s serial number for a new node: one past the greatest. -/
def nextIno (σ : State) : Nat := ((σ.nodes.map (·.ino)).max?.getD 0) + 1

/-- Node `n` is in the tree: a root or an entry's target (a removed directory is neither). -/
def linked (σ : State) (n : Nat) : Bool :=
  σ.roots.any (·.2 == n) || σ.nodes.any fun nd => match nd.body with
    | .dir es => es.any (·.2 == n)
    | .file _ => false

/-- The directory stack after walking components `cs` from stack `st` (head = the current
directory): `.` stays, `..` pops (popping the start = an escape: `perm`), a name enters its
directory (`noent` when absent, `notdir` on a file). -/
def walk (σ : State) : List Nat → List Bytes → Except Nat (List Nat)
  | st, [] => .ok st
  | st, c :: cs =>
    if c = [46] then σ.walk st cs
    else if c = [46, 46] then match st with
      | _ :: d :: st' => σ.walk (d :: st') cs
      | _ => .error Errno.perm
    else match (σ.entries (st.headD 0)).lookup c with
      | none => .error Errno.noent
      | some n => if σ.isDir n then σ.walk (n :: st) cs else .error Errno.notdir

end State

/-- `path` split at `/` (byte 47). -/
def splitSlash : Bytes → List Bytes
  | [] => [[]]
  | b :: bs => if b = 47 then [] :: splitSlash bs else
    match splitSlash bs with
    | c :: cs => (b :: c) :: cs
    | [] => [[b]]

/-- A path resolved from directory node `d`: the directory stack holding its final component, that
component, and whether the path ends in `/`. A NUL → `inval` (wasmtime's filesystem layer); an
absolute path → `perm`; an empty one → `noent`. -/
def State.resolve (σ : State) (d : Nat) (path : Bytes) :
    Except Nat (List Nat × Bytes × Bool) :=
  if 0 ∈ path then .error Errno.inval
  else if path.head? = some 47 then .error Errno.perm
  else match (splitSlash path).filter (· ≠ []) with
    | [] => .error Errno.noent
    | cs => do
      let st ← σ.walk [d] cs.dropLast
      pure (st, cs.getLastD [], path.getLast? = some 47)

/-- The node final component `c` names in stack `st`, if any (`.` = the directory, `..` = its
parent: popping the start = `perm`). -/
def State.target (σ : State) (st : List Nat) (c : Bytes) : Except Nat (Option Nat) :=
  if c = [46] then .ok (some (st.headD 0))
  else if c = [46, 46] then match st with
    | _ :: d :: _ => .ok (some d)
    | _ => .error Errno.perm
  else .ok ((σ.entries (st.headD 0)).lookup c)

/-- The first non-empty buffer's length (0 when all are empty). -/
def firstLen (iovs : List (Nat × Nat)) : Nat := ((iovs.map (·.2)).find? (· ≠ 0)).getD 0

/-- `data` stored across the buffers in order. -/
def scatter : List (Nat × Nat) → Bytes → List (Nat × Bytes)
  | [], _ => []
  | (a, l) :: iovs, data => (a, data.take l) :: scatter iovs (data.drop l)

/-- The most bytes a host may transfer for an `fd_read`/`fd_write` request: within the buffers,
the result's u32, the data a read has left, the room a file write has below a u64 size. -/
def maxCount (σ : State) (r : Req) : Nat :=
  let total := min (r.iovs.map (·.2)).sum (2 ^ 32 - 1)
  match σ.desc (r.args.getD 0 0), r.call with
  | some ⟨.stream 0 _, _, _, _⟩, .fdRead => min total σ.stdin.length
  | some ⟨.file n pos, _, _, _⟩, .fdRead => min total ((σ.data n).length - pos)
  | some ⟨.file n pos, fl, _, _⟩, .fdWrite =>
    min total (2 ^ 64 - 1 - (if flag fl Fdflags.append then (σ.data n).length else pos))
  | _, _ => total

/-- The errno-or-effect of call `r` (`proc_exit` is `step`'s): `.error e` = errno `e`, no effect;
`.ok (τ, writes)` = the successor world and the bytes to store. -/
def run (σ : State) (r : Req) (ch : Choice) : Except Nat (State × List (Nat × Bytes)) :=
  let x := r.args.getD
  let open_ (σ' : State) (k : Kind) (rb ri ff out : Nat) :
      Except Nat (State × List (Nat × Bytes)) :=
    let fd := ch.fd.getD σ.nextFd  -- E's number from the call's start state (creation keeps fds)
    if 2 ^ 31 ≤ fd then .error Errno.mfile else
    let (b, i) := ch.rights.getD (rb, ri)
    .ok ({ σ' with fds := (fd, ⟨k, ff, b, i⟩) :: σ'.fds, free := σ'.free.erase fd },
      [(out, le 4 fd)])
  -- a new node `b` named `c` in directory `p`: none in a removed directory (POSIX rmdir: "no new
  -- entries may be created in the directory"; probe r5 `UnlinkedDirectory`); `E`'s u64 serial
  -- numbers run out at 2^64 (a named completion)
  let create (p : Nat) (c : Bytes) (b : Body) : Except Nat State :=
    if !σ.linked p then .error Errno.noent
    else if ch.ino = none ∧ 2 ^ 64 ≤ σ.nextIno then .error Errno.nospc else
    let σ' := σ.setBody p (.dir (σ.entries p ++ [(c, σ.nodes.length)]))
    .ok { σ' with nodes := σ'.nodes ++ [⟨ch.ino.getD σ.nextIno, b⟩] }
  -- `σ` without entry `c` in directory `p`
  let unlink (p : Nat) (c : Bytes) : State := σ.setBody p (.dir ((σ.entries p).filter (·.1 ≠ c)))
  -- the directory node of a path call's descriptor holding right `bit`
  let dirOf (fd bit : Nat) : Except Nat Nat :=
    match σ.desc fd with
    | some ⟨.dir n _, _, b, _⟩ => if has b bit then .ok n else .error Errno.notcapable
    | _ => .error Errno.badf  -- p1:567–573
  match r.call with
  | .argsGet => .ok (σ, entryWrites σ.args (x 0 0) (x 1 0))
  | .environGet => .ok (σ, entryWrites σ.env (x 0 0) (x 1 0))
  | .argsSizesGet => sizes σ.args
  | .environSizesGet => sizes σ.env
  | .clockTimeGet =>
    let id := x 0 0
    match ch.time with
      | some t => .ok ({ σ with clocks := σ.clocks.set id t }, [(x 2 0, le 8 t)])
      | none => if id < 2 then .ok (σ, [(x 2 0, le 8 (σ.clocks.getD id 0))])
        else .error Errno.badf  -- process + thread clocks: p1:1318
  | .fdClose =>
    match σ.desc (x 0 0) with
    | some _ => .ok ({ σ with fds := σ.fds.filter (·.1 ≠ x 0 0), free := x 0 0 :: σ.free }, [])
    | none => .error Errno.badf  -- p1:1365
  | .fdFdstatGet =>
    match σ.desc (x 0 0) with
    | some d =>
      let type := match d.kind with
        | .stream _ t => t
        | .file .. => Filetype.regularFile
        | .dir .. => Filetype.directory
      .ok (σ, [(x 1 0, [UInt8.ofNat type]), (x 1 0 + 2, le 2 d.flags), (x 1 0 + 8, le 8 d.base),
        (x 1 0 + 16, le 8 d.inh)])
    | none => .error Errno.badf
  | .fdFdstatSetFlags =>
    let fl := x 1 0
    match σ.desc (x 0 0) with
      | some d@⟨.file .., _, b, _⟩ =>
        if !has b Right.fdFdstatSetFlags then .error Errno.notcapable
        else if flag fl (Fdflags.dsync ||| Fdflags.rsync ||| Fdflags.sync) then
          .error Errno.inval  -- p1:1541–1546
        else .ok (σ.setDesc (x 0 0) { d with flags := fl }, [])
      | _ => .error Errno.badf  -- non-file: p1:520–526
  | .fdPrestatGet =>
    match σ.desc (x 0 0) with
    | some ⟨.dir _ (some g), _, _, _⟩ => .ok (σ, [(x 1 0, [0]), (x 1 0 + 4, le 4 g.length)])
    | _ => .error Errno.badf  -- p1:1828
  | .fdPrestatDirName =>
    match σ.desc (x 0 0) with
    | some ⟨.dir _ (some g), _, _, _⟩ =>
      if x 2 0 < g.length then .error Errno.nametoolong  -- p1:1846–1848
      else .ok (σ, [(x 1 0, g)])
    | some _ => .error Errno.notdir  -- p1:1852
    | none => .error Errno.badf
  | .fdRead =>
    match σ.desc (x 0 0) with
    | some ⟨.stream 0 _, _, b, _⟩ =>
      if !has b Right.fdRead then .error Errno.notcapable
      -- an empty request on stdin: p1:276–287 (probe `stdin-zero`)
      else if firstLen r.iovs = 0 ∧ ch.count = none then .error Errno.intr else
      let k := ch.count.getD (min (firstLen r.iovs) (min σ.stdin.length stdinChunk))
      .ok ({ σ with stdin := σ.stdin.drop k },
        scatter r.iovs (σ.stdin.take k) ++ [(x 3 0, le 4 k)])
    | some d@⟨.file n pos, _, b, _⟩ =>
      if !has b Right.fdRead then .error Errno.notcapable
      -- E at the off_t limit: a read reaching 2^63 → inval (Linux pread: pos + count overflows
      -- off_t; probe r5 `OffsetIO`)
      else if ch.count = none ∧ fileMax < pos + firstLen r.iovs then .error Errno.inval else
      let k := ch.count.getD (min (firstLen r.iovs) ((σ.data n).length - pos))
      .ok (σ.setDesc (x 0 0) { d with kind := .file n (pos + k) },
        scatter r.iovs (((σ.data n).drop pos).take k) ++ [(x 3 0, le 4 k)])
    | _ => .error Errno.badf  -- stdout, stderr, directories: p1:1738
  | .fdWrite =>
    let all := r.data.flatten
    match σ.desc (x 0 0) with
    | some ⟨.stream k _, _, b, _⟩ =>
      if k = 0 then .error Errno.badf  -- stdin: p1:711
      else if !has b Right.fdWrite then .error Errno.notcapable else
      let c := ch.count.getD (firstLen r.iovs)
      .ok (if k = 1 then { σ with stdout := σ.stdout ++ all.take c }
        else { σ with stderr := σ.stderr ++ all.take c }, [(x 3 0, le 4 c)])
    | some d@⟨.file n pos, fl, b, _⟩ =>
      if !has b Right.fdWrite then .error Errno.notcapable else
      let old := σ.data n
      let app := flag fl Fdflags.append
      let off := if app then old.length else pos  -- p1:651–655
      -- E at the file-size limit (wasmtime 50.0.0, Linux tmpfs; probes r5 `OffsetIO`, MAIN
      -- `Append`): a positioned write reaching 2^63 → inval (pwrite: off_t overflow); an append
      -- from `fileMax` → fbig, below it cut there. W's room is u64 (`maxCount`).
      if ch.count = none ∧ app ∧ fileMax ≤ off ∧ firstLen r.iovs ≠ 0 then .error Errno.fbig
      else if ch.count = none ∧ !app ∧ fileMax < off + firstLen r.iovs then .error Errno.inval else
      let c := ch.count.getD (min (firstLen r.iovs) (fileMax - off))
      -- a 0-byte write changes no file (pwrite; tester-5's `fd_write.zero-past-eof`)
      let new := if c = 0 then old
        else old.take off ++ List.replicate (off - old.length) 0 ++ all.take c ++ old.drop (off + c)
      .ok ((σ.setBody n (.file new)).setDesc (x 0 0) { d with kind := .file n (off + c) },
        [(x 3 0, le 4 c)])
    | _ => .error Errno.badf  -- directories: p1:711
  | .fdSeek =>
    let (delta, whence) := (x 1 0, x 2 0)
    match σ.desc (x 0 0) with
      | some ⟨.stream .., _, _, _⟩ => .error Errno.spipe  -- p1:538–543
      | some d@⟨.file n pos, _, b, _⟩ =>
        if !(has b Right.fdSeek || (delta = 0 && whence = 1 && has b Right.fdTell)) then
          .error Errno.notcapable
        else
          let from_ : Int := if whence = 0 then 0 else if whence = 1 then pos else (σ.data n).length
          let new := from_ + (if delta < 2 ^ 63 then (delta : Int) else delta - 2 ^ 64)
          if new < 0 ∨ 2 ^ 64 ≤ new then .error Errno.inval  -- p1:1902–1913
          else .ok (σ.setDesc (x 0 0) { d with kind := .file n new.toNat },
            [(x 3 0, le 8 new.toNat)])
      | _ => .error Errno.badf  -- p1:544
  | .pathOpen =>
    let (of, rb, ri, ff) := (x 4 0, x 5 0, x 6 0, x 7 0)
    match σ.desc (x 0 0) with
      | some ⟨.file .., _, _, _⟩ => .error Errno.notdir  -- p1:2189
      | some ⟨.dir dn _, _, b, inh⟩ =>
        let creat := flag of Oflags.creat
        let trunc := flag of Oflags.trunc
        -- rights WITX requires (typenames.witx rights docs)
        if !has b Right.pathOpen || (creat && !has b Right.pathCreateFile) ||
            (trunc && !has b Right.pathFilestatSetSize) ||
            (flag ff Fdflags.dsync && !(has b Right.fdDatasync || has b Right.fdSync)) ||
            ((flag ff Fdflags.rsync || flag ff Fdflags.sync) && !has b Right.fdSync) ||
            !subset rb inh || !subset ri inh then .error Errno.notcapable
        else if flag of Oflags.directory && (creat || flag of Oflags.excl || trunc) then
          .error Errno.inval
        -- W pins wasmtime 50.0.0: no sync fdflags (probe r5 `OpenFlags`: notsup on files + dirs)
        else if flag ff (Fdflags.dsync ||| Fdflags.rsync ||| Fdflags.sync) then .error Errno.notsup
        else do
          let (st, c, slash) ← σ.resolve dn r.path
          match ← σ.target st c with
          | some n =>
            if creat && flag of Oflags.excl then .error Errno.exist
            else if σ.isDir n then
              if trunc || has rb Right.fdWrite then .error Errno.isdir
              -- W pins wasmtime: a directory keeps no fdflags (p1:1472; probe r5 `OpenFlags`)
              else open_ σ (.dir n none) rb ri 0 (x 8 0)
            else if flag of Oflags.directory || slash then .error Errno.notdir
            else open_ (if trunc then σ.setBody n (.file []) else σ) (.file n 0) rb ri ff (x 8 0)
          | none =>
            if !creat then .error Errno.noent
            else if slash then .error Errno.isdir
            else
              open_ (← create (st.headD 0) c (.file [])) (.file σ.nodes.length 0) rb ri ff (x 8 0)
      | _ => .error Errno.badf  -- p1:2190
  | .pathCreateDirectory => do
    let (st, c, _) ← σ.resolve (← dirOf (x 0 0) Right.pathCreateDirectory) r.path
    match ← σ.target st c with
    | some _ => .error Errno.exist
    | none => .ok (← create (st.headD 0) c (.dir []), [])
  | .pathRemoveDirectory => do
    let (st, c, _) ← σ.resolve (← dirOf (x 0 0) Right.pathRemoveDirectory) r.path
    if c = [46] ∨ c = [46, 46] then .error Errno.inval  -- `.` + `..`: probes c13, tester-5 C89
    else match ← σ.target st c with
      | none => .error Errno.noent
      | some n =>
        if !σ.isDir n then .error Errno.notdir
        else if σ.entries n ≠ [] then .error Errno.notempty
        else .ok (unlink (st.headD 0) c, [])
  | .pathUnlinkFile => do
    let (st, c, slash) ← σ.resolve (← dirOf (x 0 0) Right.pathUnlinkFile) r.path
    if c = [46] ∨ c = [46, 46] then .error Errno.isdir
    else match ← σ.target st c with
      | none => .error Errno.noent
      | some n =>
        if σ.isDir n then .error Errno.isdir  -- WITX path_unlink_file
        else if slash then .error Errno.notdir
        else .ok (unlink (st.headD 0) c, [])
  | .pathFilestatGet => do
    let (st, c, slash) ← σ.resolve (← dirOf (x 0 0) Right.pathFilestatGet) r.path
    match ← σ.target st c with
    | none => .error Errno.noent
    | some n =>
      if slash && !σ.isDir n then .error Errno.notdir else
      let sc := ch.stat.getD ⟨1, 0, 0, 0, 0⟩
      let p := x 4 0
      .ok (σ, [(p, le 8 σ.dev), (p + 8, le 8 ((σ.nodes[n]?.map (·.ino)).getD 0)),
        (p + 16, [UInt8.ofNat (if σ.isDir n then Filetype.directory else Filetype.regularFile)]),
        (p + 24, le 8 sc.nlink),
        (p + 32, le 8 (if σ.isDir n then sc.size else (σ.data n).length)),
        (p + 40, le 8 sc.atim), (p + 48, le 8 sc.mtim), (p + 56, le 8 sc.ctim)])
  | .randomGet => .ok (σ, [(x 0 0, (ch.bytes ++ List.replicate (x 1 0) 0).take (x 1 0))])
  | .procExit => .ok (σ, [])
where
  /-- `args_get`/`environ_get`: entry `i`'s pointer at `ptrs + 4i`, its bytes + NUL consecutively
  from `buf`. -/
  entryWrites : List Bytes → Nat → Nat → List (Nat × Bytes)
    | [], _, _ => []
    | e :: es, ptrs, buf =>
      (ptrs, le 4 buf) :: (buf, e ++ [0]) :: entryWrites es (ptrs + 4) (buf + e.length + 1)
  /-- `args_sizes_get`/`environ_sizes_get`: the count and the bytes with NULs (u32 each). -/
  sizes (es : List Bytes) : Except Nat (State × List (Nat × Bytes)) :=
    let size := (es.map (·.length + 1)).sum
    if 2 ^ 32 ≤ es.length ∨ 2 ^ 32 ≤ size then .error Errno.overflow  -- p1:1223–1229
    else .ok (σ, [(r.args.getD 0 0, le 4 es.length), (r.args.getD 1 0, le 4 size)])

/-- The world step of call `r` under choice `ch`: a chosen failure first (W), then the call. -/
def step (σ : State) (r : Req) (ch : Choice) : State × Resp :=
  if r.call = .procExit then ({ σ with exited := some (r.args.getD 0 0) }, .exit (r.args.getD 0 0))
  else match ch.err with
    | some e => (σ, .err e)
    | none => match run σ r ch with
      | .ok (τ, ws) => (τ, .ok ws)
      | .error e => (σ, .err e)

/-- Call `c` on arguments `vs` with memory `mem` of store `s`: decode, step, store the outputs.
Success and failure return the errno; `proc_exit` = `trapped` with the exit in the world. -/
def exec (σ : State) (c : Call) (s : Store) (mem : Nat) (vs : List Val) (ch : Choice) :
    State × HostOutcome :=
  match s.mems[mem]?, c.args vs with
  | some m, some a =>
    match step σ (decode c m a) ch with
    | (τ, .ok ws) =>
      (τ, .returned (s.setMem mem (ws.foldl (fun m w => writeBytes m w.1 w.2) m)) [.i32 0])
    | (τ, .err e) => (τ, .returned s [.i32 (BitVec.ofNat 32 e)])
    | (τ, .exit _) => (τ, .trapped s)
  | _, _ => (σ, .trapped s)

/-- The choices W allows (`none` = `E`'s, always allowed): a failure code 1–76 for any call but
`proc_exit`; a transfer within `maxCount`, nonzero when that is; an unused descriptor below 2^31;
a u64 clock reading, monotonic for clocks 1–3; an unused u64 serial number (`inode` is u64,
typenames.witx:332–333); rights within the requested ones; u64 `filestat` fields. -/
def ChoiceOK (σ : State) (r : Req) (ch : Choice) : Prop :=
  (∀ e, ch.err = some e → 1 ≤ e ∧ e ≤ 76 ∧ r.call ≠ .procExit) ∧
  (∀ n, ch.count = some n → n ≤ maxCount σ r ∧ (0 < maxCount σ r → 0 < n)) ∧
  (∀ f, ch.fd = some f → f < 2 ^ 31 ∧ f ∉ σ.fds.map (·.1)) ∧
  (∀ t, ch.time = some t → t < 2 ^ 64 ∧
    (0 < r.args.getD 0 0 → σ.clocks.getD (r.args.getD 0 0) 0 ≤ t)) ∧
  (∀ i, ch.ino = some i → i < 2 ^ 64 ∧ i ∉ σ.nodes.map (·.ino)) ∧
  (∀ b i, ch.rights = some (b, i) → subset b (r.args.getD 5 0) ∧ subset i (r.args.getD 6 0)) ∧
  (∀ sc, ch.stat = some sc →
    sc.nlink < 2 ^ 64 ∧ sc.size < 2 ^ 64 ∧ sc.atim < 2 ^ 64 ∧ sc.mtim < 2 ^ 64 ∧ sc.ctim < 2 ^ 64)

end FVA.Wasi
