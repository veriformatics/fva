import Lean

/-!
# Sandbox for project code (trusted glue, D12)

`fva trust` and `fva explain` run the project's own code: its Lake configuration (`lake build`,
`lake env`), its modules' elaboration (`#eval`, macros, build targets) and the exporter reading
its `.olean`s. Each such process runs in `bwrap`, as `lake check` does: `/` read-only, home
directories, `/run/user` and `/tmp` covered, an empty network namespace, the environment
cleared but for `PATH`; writable alone the `.lake` directories of the project and its path
dependencies, plus the private scratch directories a caller names. A write anywhere else fails,
so project code cannot change FVA, its canaries, the toolchain or the user's files.
-/

namespace FVA.Tool.Sandbox

open Lean System

/-- Directories of the project's path dependencies (`lake-manifest.json` entries of type
`path`), resolved against `root`; a missing manifest = none. -/
def pathDeps (root : FilePath) : IO (Array FilePath) := do
  let m := root / "lake-manifest.json"
  unless ← m.pathExists do return #[]
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile m))
  let pkgs := (j.getObjValAs? (Array Json) "packages").toOption.getD #[]
  let mut out := #[]
  for p in pkgs do
    if (p.getObjValAs? String "type").toOption == some "path" then
      if let some d := (p.getObjValAs? String "dir").toOption then
        out := out.push (← IO.FS.realPath (root / d))
  return out

/-- How project code is confined (D19): `full` = every namespace unshared; `noNet` = the same
without a network namespace, chosen only where bwrap cannot create one (an agent sandbox that
denies netlink sockets) and the outer sandbox already denies sockets; `off` = `--no-sandbox`. -/
inductive Mode where
  | full | noNet | off
deriving BEq, Repr

/-- The report line for a mode. -/
def Mode.describe : Mode → String
  | .full => "bwrap (no network, the system read-only, writes to the project's .lake only)"
  | .noNet => "bwrap without its own network namespace (the outer sandbox already denies sockets)"
  | .off => "off (--no-sandbox: the project's code runs with your permissions)"

/-- `bwrap` arguments that run a command in `root` (resolved) with `writable` directories
(created when missing) writable. The toolchain (`sysroot`) and every path dependency stay
readable when they lie under a covered directory. -/
def bwrapArgs (root sysroot : FilePath) (writable : Array FilePath) (mode : Mode := .full) :
    IO (Array String) := do
  let deps ← pathDeps root
  let rw := #[root / ".lake"] ++ deps.map (· / ".lake") ++ writable
  for d in rw do IO.FS.createDirAll d
  let ro := #[sysroot, root] ++ deps
  -- the outer `PATH` stays (NixOS keeps its tools under /run/current-system); its entries under
  -- a covered directory just vanish
  let path := (← IO.getEnv "PATH").getD "/usr/local/bin:/usr/bin:/bin"
  let unshare := if mode == .full then #["--unshare-all"] else
    #["--unshare-user", "--unshare-ipc", "--unshare-pid", "--unshare-uts", "--unshare-cgroup-try"]
  return #["--die-with-parent", "--new-session"] ++ unshare ++ #["--clearenv",
      "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc",
      "--tmpfs", "/tmp", "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/run/user"] ++
    ro.flatMap (fun d => #["--ro-bind", d.toString, d.toString]) ++
    rw.flatMap (fun d => #["--bind", d.toString, d.toString]) ++
    -- the covering tmpfs read-only (the binds keep theirs): a write beside the project fails
    -- instead of landing in a throwaway directory
    #["--remount-ro", "/home", "--remount-ro", "/root", "--setenv", "HOME", "/tmp",
      "--setenv", "PATH", s!"{sysroot / "bin"}:{path}", "--chdir", root.toString]

/-- `cmd args` (an absolute binary, or one on the sandbox `PATH`) in the sandbox of project
`root`, with `env` set inside it. -/
def spawnArgs (root sysroot : FilePath) (cmd : String) (args : Array String)
    (writable : Array FilePath := #[]) (env : Array (String × String) := #[])
    (mode : Mode := .full) : IO (IO.Process.SpawnArgs) := do
  if mode == .off then return { cmd, args, cwd := root, env := env.map fun (k, v) => (k, some v) }
  let b ← bwrapArgs root sysroot writable mode
  let sets := env.flatMap fun (k, v) => #["--setenv", k, v]
  return { cmd := "bwrap", args := b ++ sets ++ #["--", cmd] ++ args, cwd := root }

/-- The sandbox cannot start here (`bwrap` missing, or user/network namespaces denied, as inside
another sandbox): its message, else `none`. -/
def unavailable (root sysroot : FilePath) : IO (Option String) := do
  let a ← spawnArgs root sysroot "true" #[]
  let o ← try IO.Process.output a catch e => return some (toString e)
  return if o.exitCode == 0 then none else some (o.stderr.trimAscii.toString)

/-- The mode for this host (D19): `full` when it starts; else `noNet` when the full sandbox fails
on its network namespace and, inside the reduced one, a TCP socket is denied (an agent sandbox
such as Codex's); else the failure's message. `noSandbox` = `off`, unchecked. -/
def choose (root sysroot : FilePath) (noSandbox : Bool := false) : IO (Except String Mode) := do
  if noSandbox then return .ok .off
  let probe (m : Mode) (cmd : String) (args : Array String) : IO IO.Process.Output := do
    try IO.Process.output (← spawnArgs root sysroot cmd args (mode := m))
    catch e => return { exitCode := 127, stdout := "", stderr := toString e }
  let o ← probe .full "true" #[]
  if o.exitCode == 0 then return .ok .full
  let err := o.stderr.trimAscii.toString
  unless (err.splitOn "NETLINK").length > 1 || (err.splitOn "loopback").length > 1 do
    return .error err
  let n ← probe .noNet "bash" #["-c", "exec 3<>/dev/tcp/127.0.0.1/9"]
  if (n.stderr.splitOn "Operation not permitted").length > 1 then return .ok .noNet
  return .error s!"{err} (and TCP sockets are not denied around it)"

/-- Lake's environment for project `root` (`lake env`, run sandboxed: the project's Lake
configuration is project code): each `KEY=VALUE` line; `none` when Lake fails. -/
def lakeEnv (root sysroot : FilePath) (mode : Mode := .full) :
    IO (Option (Array (String × Option String))) := do
  let o ← IO.Process.output (← spawnArgs root sysroot (sysroot / "bin" / "lake").toString
    #["env"] (mode := mode))
  if o.exitCode != 0 then return none
  return some <| (o.stdout.splitOn "\n").toArray.filterMap fun l =>
    match l.splitOn "=" with
    | k :: v@(_ :: _) => some (k, some ("=".intercalate v))
    | _ => none

end FVA.Tool.Sandbox
