import FVA.Spec.Wasi.Abi

/-!
# WASI process state (reviewed spec)

The world a WASI process acts on: its arguments + environment, the three stdio streams (`stdin` =
the unread input, finite; `stdout`/`stderr` = the bytes written so far), its descriptors, the file
system as nodes addressed by index (a file's identity is apart from its paths and descriptors: an
unlinked file stays readable through an open descriptor), the preopened directories (`roots`), the
four clocks' last readings and the exit status. `State.init` builds a process from directory trees
(one per `--dir`); `State.spawn` = the next process of a pipeline, reading the previous one's
whole stdout.
-/

namespace FVA.Wasi

/-- Byte strings: file contents, names, streams. -/
abbrev Bytes := List UInt8

/-- A file's contents, or a directory's entries (name ↦ node index). -/
inductive Body where
  | file (data : Bytes)
  | dir (entries : List (Bytes × Nat))

/-- A file system node: its serial number (`filestat.ino`) and body. -/
structure Node where
  /-- Serial number. -/
  ino : Nat
  /-- Contents or entries. -/
  body : Body

/-- What a descriptor names: a stdio stream (`k`: 0 stdin, 1 stdout, 2 stderr; its reported file
type), an open file (node + offset), or a directory (node; `pre` = a preopen's guest name). -/
inductive Kind where
  | stream (k type : Nat)
  | file (node pos : Nat)
  | dir (node : Nat) (pre : Option Bytes)

/-- A descriptor: what it names, its `fdflags`, its base + inheriting rights. -/
structure Desc where
  /-- What it names. -/
  kind : Kind
  /-- Its `fdflags`. -/
  flags : Nat
  /-- Base rights. -/
  base : Nat
  /-- Inheriting rights. -/
  inh : Nat

/-- The world of one WASI process. -/
structure State where
  /-- Arguments, argv[0] first. -/
  args : List Bytes
  /-- Environment entries `K=V`. -/
  env : List Bytes
  /-- The unread input. -/
  stdin : Bytes
  /-- The bytes written to stdout so far. -/
  stdout : Bytes
  /-- The bytes written to stderr so far. -/
  stderr : Bytes
  /-- Open descriptors by number. -/
  fds : List (Nat × Desc)
  /-- Closed descriptor numbers (reused greatest first, as wasmtime does). -/
  free : List Nat
  /-- File system nodes by index. -/
  nodes : List Node
  /-- Preopened directories: guest name + node. -/
  roots : List (Bytes × Nat)
  /-- The last reading of each clock id 0–3 (ns). -/
  clocks : List Nat
  /-- The device number every `filestat` reports. -/
  dev : Nat
  /-- `some k` once the process called `proc_exit k`. -/
  exited : Option Nat

/-- A directory tree given at start (the contents of one `--dir`). -/
inductive Tree where
  | file (data : Bytes)
  | dir (entries : List (Bytes × Tree))

mutual
/-- The nodes in `t`. -/
def Tree.size : Tree → Nat
  | .file _ => 1
  | .dir es => 1 + Tree.sizes es
/-- The nodes in the entries' trees. -/
def Tree.sizes : List (Bytes × Tree) → Nat
  | [] => 0
  | (_, t) :: es => t.size + Tree.sizes es
end

/-- Each entry's name and node index, the entries' trees numbered consecutively from `k`. -/
def Tree.links (k : Nat) : List (Bytes × Tree) → List (Bytes × Nat)
  | [] => []
  | (n, t) :: es => (n, k) :: Tree.links (k + t.size) es

mutual
/-- The bodies of `t`'s nodes numbered depth-first from `k` (`t` itself = node `k`). -/
def Tree.flat (k : Nat) : Tree → List Body
  | .file d => [.file d]
  | .dir es => .dir (Tree.links (k + 1) es) :: Tree.flats (k + 1) es
/-- The bodies of the entries' trees, numbered consecutively from `k`. -/
def Tree.flats (k : Nat) : List (Bytes × Tree) → List Body
  | [] => []
  | (_, t) :: es => t.flat k ++ Tree.flats (k + t.size) es
end

/-- A valid entry name: nonempty, without `/` or NUL, neither `.` nor `..`. -/
def Name.Ok (n : Bytes) : Prop := n ≠ [] ∧ 47 ∉ n ∧ 0 ∉ n ∧ n ≠ [46] ∧ n ≠ [46, 46]

mutual
/-- Every directory's entries have valid, distinct names; files fit a u64 size. -/
def Tree.Wf : Tree → Prop
  | .file d => d.length < 2 ^ 64
  | .dir es => (es.map (·.1)).Nodup ∧ Tree.WfList es
/-- Every entry's name is valid and its tree well formed. -/
def Tree.WfList : List (Bytes × Tree) → Prop
  | [] => True
  | (n, t) :: es => Name.Ok n ∧ t.Wf ∧ Tree.WfList es
end

/-- Valid start inputs: each preopen a well-formed directory tree, four clock readings below
2^64. -/
def InitOK (dirs : List (Bytes × Tree)) (clocks : List Nat) : Prop :=
  (∀ d ∈ dirs, d.2.Wf ∧ ∃ es, d.2 = .dir es) ∧ clocks.length = clockCount ∧
    ∀ t ∈ clocks, t < 2 ^ 64

/-- The base rights of a preopened directory: wasmtime 50.0.0's hard-coded set (p1:1432–1446)
plus `fd_datasync`, `fd_sync` and `path_filestat_set_size`, which WITX requires for `path_open`
with `dsync`/`rsync`/`sync` and `trunc` (wasmtime does not enforce rights). -/
def preBase : Nat :=
  rights [Right.fdDatasync, Right.fdSync, Right.pathCreateDirectory, Right.pathCreateFile,
    Right.pathLinkSource, Right.pathLinkTarget, Right.pathOpen, Right.fdReaddir,
    Right.pathReadlink, Right.pathRenameSource, Right.pathRenameTarget, Right.pathSymlink,
    Right.pathRemoveDirectory, Right.pathUnlinkFile, Right.pathFilestatGet,
    Right.pathFilestatSetSize, Right.pathFilestatSetTimes, Right.fdFilestatGet,
    Right.fdFilestatSetTimes]

/-- The inheriting rights of a preopened directory: wasmtime's (its base + the file rights,
p1:1448–1461) plus `path_filestat_set_size`. -/
def preInh : Nat :=
  preBase ||| rights [Right.fdRead, Right.fdSeek, Right.fdFdstatSetFlags, Right.fdTell,
    Right.fdWrite, Right.fdAdvise, Right.fdAllocate, Right.fdFilestatSetSize,
    Right.pollFdReadwrite]

/-- The descriptors of a fresh process: stdin, stdout, stderr (non-tty streams with wasmtime's
stdio rights, p1:1410–1426), then each root at 3, 4, … -/
def initFds (roots : List (Bytes × Nat)) : List (Nat × Desc) :=
  [(0, ⟨.stream 0 Filetype.unknown, 0, rights [Right.fdRead], rights [Right.fdRead]⟩),
   (1, ⟨.stream 1 Filetype.unknown, 0, rights [Right.fdWrite], rights [Right.fdWrite]⟩),
   (2, ⟨.stream 2 Filetype.unknown, 0, rights [Right.fdWrite], rights [Right.fdWrite]⟩)] ++
  roots.mapIdx fun i r => (3 + i, ⟨.dir r.2 (some r.1), 0, preBase, preInh⟩)

/-- The nodes of the preopened trees, numbered in order, and each tree's guest name + root node. -/
def initNodes (dirs : List (Bytes × Tree)) : List Body × List (Bytes × Nat) :=
  dirs.foldl (fun acc d => (acc.1 ++ d.2.flat acc.1.length, acc.2 ++ [(d.1, acc.1.length)]))
    ([], [])

/-- A process started with `args`, `env`, `stdin`, the preopened `dirs` (guest name + tree) and
the clocks' readings `clocks` (ids 0–3): node `i` has serial number `i + 1`, device 1. -/
def State.init (args env : List Bytes) (stdin : Bytes) (dirs : List (Bytes × Tree))
    (clocks : List Nat) : State :=
  { args, env, stdin, stdout := [], stderr := [], fds := initFds (initNodes dirs).2, free := [],
    nodes := (initNodes dirs).1.mapIdx fun i b => ⟨i + 1, b⟩, roots := (initNodes dirs).2,
    clocks, dev := 1, exited := none }

/-- The next process of a pipeline `p₁ | p₂`, started once `p₁` (state `σ`) has finished: fresh
descriptors over the same roots, stdin = `p₁`'s whole stdout, CPU clocks at 0; files, environment,
stderr and the realtime + monotonic readings carry over. -/
def State.spawn (σ : State) (args : List Bytes) : State :=
  { σ with
    args := args
    stdin := σ.stdout
    stdout := []
    fds := initFds σ.roots
    free := []
    clocks := (σ.clocks.set 2 0).set 3 0
    exited := none }

/-- The node reached from node `d` through the entry names `ns`. -/
def State.walkNames (σ : State) (d : Nat) : List Bytes → Option Nat
  | [] => some d
  | n :: ns => match σ.nodes[d]? with
    | some ⟨_, .dir es⟩ => (es.lookup n).bind (σ.walkNames · ns)
    | _ => none

/-- The contents of the file at `path` (entry names) under the root named `root`. -/
def State.fileAt (σ : State) (root : Bytes) (path : List Bytes) : Option Bytes :=
  match (σ.roots.lookup root).bind (σ.walkNames · path) |>.bind (σ.nodes[·]?) with
  | some ⟨_, .file d⟩ => some d
  | _ => none

/-- The entries of node `n` (none for a file). -/
def State.entries (σ : State) (n : Nat) : List (Bytes × Nat) :=
  match σ.nodes[n]? with
  | some ⟨_, .dir es⟩ => es
  | _ => []

/-- Node `n` is a directory. -/
def State.isDir (σ : State) (n : Nat) : Bool :=
  match σ.nodes[n]? with
  | some ⟨_, .dir _⟩ => true
  | _ => false

/-- Node `n` is a file. -/
def State.isFile (σ : State) (n : Nat) : Bool :=
  match σ.nodes[n]? with
  | some ⟨_, .file _⟩ => true
  | _ => false

/-- A body's size: a file's length (a directory: 0). -/
def Body.size : Body → Nat
  | .file d => d.length
  | .dir _ => 0

/-- A descriptor names a stream, or a node of its kind (a file at an offset below 2^64). -/
def Desc.Ok (σ : State) (d : Desc) : Prop :=
  match d.kind with
  | .stream k _ => k < 3
  | .file n pos => σ.isFile n ∧ pos < 2 ^ 64
  | .dir n _ => σ.isDir n

/-- A well-formed state (decidable): descriptor numbers distinct, below 2^31 and apart from the
distinct `free` ones; each descriptor and root names a node of its kind; directory entries carry
valid distinct names and existing nodes; no node is the target of two entries or of an entry and
a root (no hard links, no root inside a tree), roots distinct; serial numbers distinct; serial
numbers, sizes and the four clock readings below 2^64. -/
def State.Wf (σ : State) : Prop :=
  (σ.fds.map (·.1)).Nodup ∧ σ.free.Nodup ∧
  (∀ e ∈ σ.fds, e.1 < 2 ^ 31 ∧ e.1 ∉ σ.free ∧ e.2.Ok σ) ∧ (∀ f ∈ σ.free, f < 2 ^ 31) ∧
  (∀ r ∈ σ.roots, σ.isDir r.2) ∧
  (∀ n < σ.nodes.length, ((σ.entries n).map (·.1)).Nodup ∧
    ∀ e ∈ σ.entries n, Name.Ok e.1 ∧ e.2 < σ.nodes.length) ∧
  (∀ p < σ.nodes.length, ∀ q < σ.nodes.length, ∀ e ∈ σ.entries p, ∀ f ∈ σ.entries q,
    e.2 = f.2 → p = q ∧ e = f) ∧
  (σ.roots.map (·.2)).Nodup ∧
  (∀ r ∈ σ.roots, ∀ p < σ.nodes.length, ∀ e ∈ σ.entries p, e.2 ≠ r.2) ∧
  (σ.nodes.map (·.ino)).Nodup ∧ (∀ n ∈ σ.nodes, n.ino < 2 ^ 64 ∧ n.body.size < 2 ^ 64) ∧
  σ.clocks.length = clockCount ∧ ∀ t ∈ σ.clocks, t < 2 ^ 64

end FVA.Wasi
