;; A caller for the ORIGINAL module, not a reimplementation of its arithmetic.
(module $probe
  (import "env" "memory" (memory 1))
  (import "edge" "calc_cpm_raw" (func $raw (param i32 i32 i32 i32)))

  ;; wasm32 cmx layout from src/edgeR.h (8 fields, 32 bytes):
  ;; dmat, imat, nrow, ncol, type, isint, pnrow, rowsel.
  ;; y at 65536; libraries at 65568; lib data at 65600; output at 65616.
  (func $setup (param $nr i32) (param $nc i32)
    (i32.store (i32.const 65536) (i32.const 65616))
    (i32.store offset=8 (i32.const 65536) (local.get $nr))
    (i32.store offset=12 (i32.const 65536) (local.get $nc))
    (i32.store offset=24 (i32.const 65536) (local.get $nr))
    (i32.store (i32.const 65568) (i32.const 65600))
    (i32.store offset=8 (i32.const 65568) (local.get $nr))
    (i32.store offset=12 (i32.const 65568) (local.get $nc))
    (i32.store offset=16 (i32.const 65568) (i32.const 2)) ;; repeated row
    (i32.store offset=24 (i32.const 65568) (i32.const 1)))
  (func $call
    (call $raw (i32.const 65536) (i32.const 65568) (i32.const 65616) (i32.const 1)))

  (func (export "scalar") (param $c f64) (param $L f64) (result f64)
    (call $setup (i32.const 1) (i32.const 1))
    (f64.store (i32.const 65600) (local.get $L))
    (f64.store (i32.const 65616) (local.get $c))
    (call $call)
    (f64.load (i32.const 65616)))

  ;; A comparison expression; this does not replace the original kernel call.
  (func (export "divide_first") (param $c f64) (param $L f64) (result f64)
    (f64.mul (f64.div (local.get $c) (local.get $L)) (f64.const 1000000)))

  ;; Two genes, two samples: columns (10,8), (10,8), library sizes 18,18.
  ;; Return an actual cell of the kernel's matrix output.
  (func (export "matrix_cell") (param $i i32) (result f64)
    (call $setup (i32.const 2) (i32.const 2))
    (f64.store (i32.const 65600) (f64.const 18))
    (f64.store (i32.const 65608) (f64.const 18))
    (f64.store (i32.const 65616) (f64.const 10))
    (f64.store (i32.const 65624) (f64.const 8))
    (f64.store (i32.const 65632) (f64.const 10))
    (f64.store (i32.const 65640) (f64.const 8))
    (call $call)
    (f64.load (i32.add (i32.const 65616) (i32.mul (local.get $i) (i32.const 8)))))
)
