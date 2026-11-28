import FVATest.Subjects.Bustools.Lifted

/-!
# bustools count-only build: the link to its bytes (U29c test claim; D28's claim = U29f)

`bustools-count.wasm` = `build`'s output (bustools `d4d7a283` + `stubs.cpp`, wasi-sdk 34.0,
sha256-pinned; fetched, never committed). Its code section exceeds `fva lift`'s threshold, so
`Lifted.decode_eq` is assembled from chunks; `fva trust` replays it with this claim.
-/

namespace Subjects.Bustools

/-- The build imports exactly these WASI preview1 functions, in this order. -/
@[fva_claim] def wasiImports : Prop :=
  Lifted.module.imports.map (fun i => (i.module, i.name)) =
    ["args_get", "args_sizes_get", "environ_get", "environ_sizes_get", "clock_time_get",
      "fd_close", "fd_fdstat_get", "fd_fdstat_set_flags", "fd_prestat_get",
      "fd_prestat_dir_name", "fd_read", "fd_seek", "fd_write", "path_create_directory",
      "path_filestat_get", "path_open", "path_remove_directory", "path_unlink_file",
      "proc_exit", "random_get"].map (("wasi_snapshot_preview1", ·))

end Subjects.Bustools
