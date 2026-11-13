;; U28b S2/R4: address identity, aliases and caller-vs-callee tag maps.
(module $origin
  (tag $noise (export "noise") (param i32))
  (tag $shared (export "shared") (param i32))
  (export "alias" (tag $shared))
  (func (export "shared-throw") (param i32) (result i32)
    local.get 0 throw $shared)
  (func (export "noise-throw") (param i32) (result i32)
    local.get 0 throw $noise))
(register "origin" $origin)

(module $catcher
  (import "origin" "shared" (tag $shared (param i32)))
  (import "origin" "noise" (tag $noise (param i32)))
  (import "origin" "alias" (tag $alias (param i32)))
  (import "origin" "shared-throw" (func $shared-throw (param i32) (result i32)))
  (import "origin" "noise-throw" (func $noise-throw (param i32) (result i32)))
  (tag $own (export "own-tag") (param i32))
  (func (export "own-throw") (param i32) (result i32)
    local.get 0 throw $own)
  (func (export "shared") (param i32) (result i32)
    (block $correct (result i32)
      (block $wrong (result i32)
        (try_table (result i32) (catch $noise $wrong) (catch $shared $correct)
          local.get 0 call $shared-throw))
      i32.const 1000
      i32.add))
  (func (export "alias") (param i32) (result i32)
    (block $correct (result i32)
      (try_table (result i32) (catch $alias $correct)
        local.get 0 call $shared-throw)))
  (func (export "noise") (param i32) (result i32)
    (block $correct (result i32)
      (block $wrong (result i32)
        (try_table (result i32) (catch $shared $wrong) (catch $noise $correct)
          local.get 0 call $noise-throw))
      i32.const 2000
      i32.add))
  (func (export "own") (param i32) (result i32)
    (block $correct (result i32)
      (block $wrong (result i32)
        (try_table (catch $shared $wrong) (catch $own $correct)
          local.get 0 throw $own)
        unreachable)
      i32.const 3000
      i32.add)))
(register "catcher" $catcher)

(assert_return (invoke $catcher "shared" (i32.const 239)) (i32.const 239)) ;; @covers S2.tag-identity,S2.handler-frame,S2.cross-module
(assert_return (invoke $catcher "alias" (i32.const 241)) (i32.const 241)) ;; @covers S2.tag-identity,S2.cross-module
(assert_return (invoke $catcher "noise" (i32.const 251)) (i32.const 251)) ;; @covers S2.handler-frame
(assert_return (invoke $catcher "own" (i32.const 257)) (i32.const 257)) ;; @covers R4.tag-alloc

(module $later
  (import "catcher" "own-tag" (tag $own (param i32)))
  (import "origin" "shared" (tag $shared (param i32)))
  (import "catcher" "own-throw" (func $own-throw (param i32) (result i32)))
  (tag $fresh (export "fresh-tag") (param i32))
  (func (export "own") (param i32) (result i32)
    (block $correct (result i32)
      (block $wrong (result i32)
        (try_table (result i32) (catch $shared $wrong) (catch $fresh $wrong) (catch $own $correct)
          local.get 0 call $own-throw))
      i32.const 4000
      i32.add))
  (func (export "fresh") (param i32) (result i32)
    (block $correct (result i32)
      (block $wrong (result i32)
        (try_table (catch $own $wrong) (catch $shared $wrong) (catch $fresh $correct)
          local.get 0 throw $fresh)
        unreachable)
      i32.const 5000
      i32.add)))

(assert_return (invoke $later "own" (i32.const 263)) (i32.const 263)) ;; @covers R4.tag-alloc,S2.cross-module
(assert_return (invoke $later "fresh" (i32.const 269)) (i32.const 269)) ;; @covers R4.tag-alloc
(assert_return (invoke $catcher "shared" (i32.const 271)) (i32.const 271)) ;; @covers R4.tag-alloc,S2.handler-frame
(assert_return (invoke $catcher "alias" (i32.const 277)) (i32.const 277)) ;; @covers S2.tag-identity
