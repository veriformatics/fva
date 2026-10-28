(module
  (type (;0;) (func (param i32 i32 i32 i32 i32 i32) (result i32)))
  (type (;1;) (func (param i32 i32 i32 i32) (result i32)))
  (type (;2;) (func (param i32 i32 i32) (result i32)))
  (memory (;0;) 32 32)
  (global (;0;) (mut i32) i32.const 65536)
  (export "memory" (memory 0))
  (export "LZ4_compress_default" (func 1))
  (export "LZ4_decompress_safe" (func 2))
  (func (;0;) (type 0) (param i32 i32 i32 i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    i32.const 0
    local.set 6
    i32.const 0
    local.set 7
    block ;; label = @1
      local.get 0
      i32.eqz
      br_if 0 (;@1;)
      i32.const 0
      local.set 7
      local.get 0
      i32.const 3
      i32.and
      br_if 0 (;@1;)
      local.get 0
      i32.const 0
      i32.const 16404
      call 5
      drop
      local.get 0
      local.set 7
    end
    local.get 5
    i32.const 1
    local.get 5
    i32.const 1
    i32.gt_s
    select
    local.tee 0
    i32.const 65537
    i32.lt_s
    local.set 5
    block ;; label = @1
      local.get 3
      i32.const 2113929216
      i32.gt_u
      br_if 0 (;@1;)
      local.get 3
      local.get 3
      i32.const 255
      i32.div_u
      i32.add
      i32.const 16
      i32.add
      local.set 6
    end
    local.get 0
    i32.const 65537
    local.get 5
    select
    local.set 8
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          local.get 4
          local.get 6
          i32.lt_s
          br_if 0 (;@3;)
          local.get 3
          i32.const 65546
          i32.gt_s
          br_if 1 (;@2;)
          block ;; label = @4
            local.get 3
            i32.const 2113929216
            i32.le_u
            br_if 0 (;@4;)
            i32.const 0
            return
          end
          block ;; label = @4
            local.get 3
            br_if 0 (;@4;)
            local.get 2
            i32.const 0
            call $store_checked_0
            i32.const 1
            return
          end
          local.get 7
          i32.const 3
          call $store_checked_1
          local.get 7
          local.get 7
          i32.const 16400
          i32.const 4
          call $readcheck
          i32.load offset=16400
          local.get 3
          i32.add
          call $store_checked_2
          local.get 7
          local.get 7
          i32.const 16392
          i32.const 4
          call $readcheck
          i32.load offset=16392
          local.tee 9
          local.get 3
          i32.add
          call $store_checked_3
          local.get 1
          local.get 3
          i32.add
          local.set 10
          block ;; label = @4
            local.get 3
            i32.const 13
            i32.ge_u
            br_if 0 (;@4;)
            local.get 2
            local.set 11
            local.get 1
            local.set 0
            br 3 (;@1;)
          end
          local.get 10
          i32.const -5
          i32.add
          local.set 12
          local.get 10
          i32.const -11
          i32.add
          local.set 13
          local.get 1
          local.get 9
          i32.sub
          local.set 14
          local.get 7
          local.get 1
          i32.const 0
          i32.const 4
          call $readcheck
          i32.load align=1
          i32.const -1640531535
          i32.mul
          i32.const 18
          i32.shr_u
          i32.const 16382
          i32.and
          i32.add
          local.get 9
          call $store_checked_4
          local.get 1
          i32.const 0
          local.get 9
          i32.sub
          i32.add
          local.set 15
          local.get 10
          i32.const -6
          i32.add
          local.set 16
          local.get 10
          i32.const -8
          i32.add
          local.set 5
          local.get 8
          i32.const 6
          i32.shl
          local.set 8
          local.get 2
          local.set 11
          local.get 1
          local.set 0
          loop ;; label = @4
            local.get 0
            i32.const 1
            i32.add
            local.set 3
            local.get 0
            i32.const 1
            i32.const 4
            call $readcheck
            i32.load offset=1 align=1
            local.set 6
            i32.const 1
            local.set 17
            local.get 8
            local.set 4
            loop ;; label = @5
              local.get 3
              local.tee 18
              local.get 17
              i32.add
              local.tee 3
              local.get 13
              i32.gt_u
              br_if 4 (;@1;)
              local.get 7
              local.get 6
              i32.const -1640531535
              i32.mul
              i32.const 18
              i32.shr_u
              i32.const 16382
              i32.and
              i32.add
              local.tee 17
              i32.const 0
              i32.const 2
              call $readcheck
              i32.load16_u
              local.set 19
              local.get 17
              local.get 18
              local.get 14
              i32.sub
              call $store_checked_4
              local.get 4
              i32.const 6
              i32.shr_u
              local.set 17
              local.get 14
              local.get 19
              i32.add
              local.tee 20
              i32.const 0
              i32.const 4
              call $readcheck
              i32.load align=1
              local.get 6
              i32.ne
              local.set 21
              local.get 3
              i32.const 0
              i32.const 4
              call $readcheck
              i32.load align=1
              local.set 6
              local.get 4
              i32.const 1
              i32.add
              local.set 4
              local.get 21
              br_if 0 (;@5;)
            end
            block ;; label = @5
              block ;; label = @6
                local.get 19
                local.get 9
                i32.sub
                i32.const 1
                i32.lt_s
                br_if 0 (;@6;)
                local.get 18
                i32.const -1
                i32.add
                local.tee 17
                i32.const 0
                i32.const 1
                call $readcheck
                i32.load8_u
                local.get 20
                i32.const -1
                i32.add
                local.tee 6
                i32.const 0
                i32.const 1
                call $readcheck
                i32.load8_u
                i32.ne
                br_if 0 (;@6;)
                local.get 9
                local.get 19
                i32.sub
                i32.const -2
                i32.gt_s
                br_if 1 (;@5;)
                local.get 17
                local.get 0
                i32.le_u
                br_if 1 (;@5;)
                local.get 15
                local.get 19
                i32.add
                local.set 19
                i32.const 0
                local.set 3
                block ;; label = @7
                  block ;; label = @8
                    loop ;; label = @9
                      local.get 18
                      local.get 3
                      i32.add
                      local.tee 17
                      i32.const -2
                      i32.add
                      local.tee 4
                      i32.const 0
                      i32.const 1
                      call $readcheck
                      i32.load8_u
                      local.get 19
                      local.get 3
                      i32.add
                      local.tee 21
                      i32.const -2
                      i32.add
                      local.tee 6
                      i32.const 0
                      i32.const 1
                      call $readcheck
                      i32.load8_u
                      i32.ne
                      br_if 1 (;@8;)
                      local.get 3
                      i32.const -1
                      i32.add
                      local.set 3
                      local.get 6
                      local.get 1
                      i32.le_u
                      br_if 2 (;@7;)
                      local.get 4
                      local.get 0
                      i32.le_u
                      br_if 2 (;@7;)
                      br 0 (;@9;)
                    end
                  end
                  local.get 17
                  i32.const -1
                  i32.add
                  local.set 17
                  local.get 21
                  i32.const -1
                  i32.add
                  local.set 6
                  br 2 (;@5;)
                end
                local.get 18
                local.get 3
                i32.add
                i32.const -1
                i32.add
                local.set 17
                local.get 19
                local.get 3
                i32.add
                i32.const -1
                i32.add
                local.set 6
                br 1 (;@5;)
              end
              local.get 18
              local.set 17
              local.get 20
              local.set 6
            end
            local.get 11
            i32.const 1
            i32.add
            local.set 3
            block ;; label = @5
              block ;; label = @6
                local.get 17
                local.get 0
                i32.sub
                local.tee 18
                i32.const 15
                i32.lt_u
                br_if 0 (;@6;)
                local.get 11
                i32.const 240
                call $store_checked_0
                block ;; label = @7
                  local.get 18
                  i32.const -15
                  i32.add
                  local.tee 4
                  i32.const 255
                  i32.lt_u
                  br_if 0 (;@7;)
                  loop ;; label = @8
                    local.get 3
                    i32.const 255
                    call $store_checked_0
                    local.get 3
                    i32.const 1
                    i32.add
                    local.set 3
                    local.get 4
                    i32.const -255
                    i32.add
                    local.tee 4
                    i32.const 254
                    i32.gt_u
                    br_if 0 (;@8;)
                  end
                end
                local.get 3
                local.get 4
                call $store_checked_0
                local.get 3
                i32.const 1
                i32.add
                local.set 3
                br 1 (;@5;)
              end
              local.get 11
              local.get 18
              i32.const 4
              i32.shl
              call $store_checked_0
            end
            local.get 3
            local.get 18
            i32.add
            local.set 18
            loop ;; label = @5
              local.get 3
              local.get 0
              i32.const 8
              call 3
              drop
              local.get 0
              i32.const 8
              i32.add
              local.set 0
              local.get 3
              i32.const 8
              i32.add
              local.tee 3
              local.get 18
              i32.lt_u
              br_if 0 (;@5;)
            end
            loop ;; label = @5
              local.get 18
              local.get 17
              local.get 6
              i32.sub
              call $store_checked_5
              local.get 6
              i32.const 4
              i32.add
              local.set 0
              local.get 18
              i32.const 2
              i32.add
              local.set 19
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    block ;; label = @9
                      block ;; label = @10
                        local.get 17
                        i32.const 4
                        i32.add
                        local.tee 21
                        local.get 5
                        i32.lt_u
                        br_if 0 (;@10;)
                        local.get 21
                        local.set 3
                        br 1 (;@9;)
                      end
                      local.get 0
                      i32.const 0
                      i32.const 4
                      call $readcheck
                      i32.load align=1
                      local.tee 3
                      local.get 21
                      i32.const 0
                      i32.const 4
                      call $readcheck
                      i32.load align=1
                      local.tee 0
                      i32.ne
                      br_if 1 (;@8;)
                      local.get 6
                      i32.const 8
                      i32.add
                      local.set 0
                      local.get 17
                      i32.const 8
                      i32.add
                      local.set 3
                    end
                    block ;; label = @9
                      block ;; label = @10
                        local.get 3
                        local.get 5
                        i32.ge_u
                        br_if 0 (;@10;)
                        loop ;; label = @11
                          block ;; label = @12
                            local.get 0
                            i32.const 0
                            i32.const 4
                            call $readcheck
                            i32.load align=1
                            local.tee 6
                            local.get 3
                            i32.const 0
                            i32.const 4
                            call $readcheck
                            i32.load align=1
                            local.tee 4
                            i32.eq
                            br_if 0 (;@12;)
                            local.get 3
                            local.get 4
                            local.get 6
                            i32.xor
                            i32.ctz
                            i32.const 3
                            i32.shr_u
                            i32.add
                            local.set 3
                            br 3 (;@9;)
                          end
                          local.get 0
                          i32.const 4
                          i32.add
                          local.set 0
                          local.get 3
                          i32.const 4
                          i32.add
                          local.tee 3
                          local.get 5
                          i32.lt_u
                          br_if 0 (;@11;)
                        end
                      end
                      block ;; label = @10
                        local.get 3
                        local.get 16
                        i32.ge_u
                        br_if 0 (;@10;)
                        local.get 0
                        i32.const 0
                        i32.const 2
                        call $readcheck
                        i32.load16_u align=1
                        local.get 3
                        i32.const 0
                        i32.const 2
                        call $readcheck
                        i32.load16_u align=1
                        i32.ne
                        br_if 0 (;@10;)
                        local.get 0
                        i32.const 2
                        i32.add
                        local.set 0
                        local.get 3
                        i32.const 2
                        i32.add
                        local.set 3
                      end
                      local.get 3
                      local.get 12
                      i32.ge_u
                      br_if 0 (;@9;)
                      local.get 3
                      local.get 0
                      i32.const 0
                      i32.const 1
                      call $readcheck
                      i32.load8_u
                      local.get 3
                      i32.const 0
                      i32.const 1
                      call $readcheck
                      i32.load8_u
                      i32.eq
                      i32.add
                      local.set 3
                    end
                    local.get 17
                    local.get 3
                    local.get 21
                    i32.sub
                    local.tee 3
                    i32.add
                    i32.const 4
                    i32.add
                    local.set 17
                    local.get 3
                    i32.const 15
                    i32.lt_u
                    br_if 1 (;@7;)
                    local.get 11
                    local.get 11
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    i32.const 15
                    i32.add
                    call $store_checked_0
                    local.get 19
                    i32.const -1
                    call $store_checked_6
                    block ;; label = @9
                      local.get 3
                      i32.const -15
                      i32.add
                      local.tee 0
                      i32.const 1020
                      i32.lt_u
                      br_if 0 (;@9;)
                      local.get 18
                      i32.const 6
                      i32.add
                      local.set 3
                      loop ;; label = @10
                        local.get 3
                        i32.const -1
                        call $store_checked_6
                        local.get 3
                        i32.const 4
                        i32.add
                        local.set 3
                        local.get 0
                        i32.const -1020
                        i32.add
                        local.tee 0
                        i32.const 1019
                        i32.gt_u
                        br_if 0 (;@10;)
                      end
                      local.get 3
                      i32.const -4
                      i32.add
                      local.set 19
                    end
                    local.get 19
                    local.get 0
                    i32.const 65535
                    i32.and
                    i32.const 255
                    i32.div_u
                    local.tee 3
                    i32.add
                    local.tee 6
                    local.get 0
                    local.get 3
                    i32.add
                    call $store_checked_0
                    local.get 6
                    i32.const 1
                    i32.add
                    local.set 19
                    br 2 (;@6;)
                  end
                  local.get 17
                  local.get 0
                  local.get 3
                  i32.xor
                  i32.ctz
                  i32.const 3
                  i32.shr_u
                  local.tee 3
                  i32.add
                  i32.const 4
                  i32.add
                  local.set 17
                end
                local.get 11
                local.get 11
                i32.const 0
                i32.const 1
                call $readcheck
                i32.load8_u
                local.get 3
                i32.add
                call $store_checked_0
              end
              block ;; label = @6
                local.get 17
                local.get 13
                i32.lt_u
                br_if 0 (;@6;)
                local.get 19
                local.set 11
                local.get 17
                local.set 0
                br 5 (;@1;)
              end
              local.get 7
              local.get 17
              i32.const -2
              i32.add
              local.tee 3
              i32.const 0
              i32.const 4
              call $readcheck
              i32.load align=1
              i32.const -1640531535
              i32.mul
              i32.const 18
              i32.shr_u
              i32.const 16382
              i32.and
              i32.add
              local.get 3
              local.get 14
              i32.sub
              call $store_checked_4
              local.get 7
              local.get 17
              i32.const 0
              i32.const 4
              call $readcheck
              i32.load align=1
              local.tee 3
              i32.const -1640531535
              i32.mul
              i32.const 18
              i32.shr_u
              i32.const 16382
              i32.and
              i32.add
              local.tee 0
              i32.const 0
              i32.const 2
              call $readcheck
              i32.load16_u
              local.set 6
              local.get 0
              local.get 17
              local.get 14
              i32.sub
              call $store_checked_4
              block ;; label = @6
                local.get 3
                local.get 14
                local.get 6
                i32.add
                local.tee 6
                i32.const 0
                i32.const 4
                call $readcheck
                i32.load align=1
                i32.eq
                br_if 0 (;@6;)
                local.get 19
                local.set 11
                local.get 17
                local.set 0
                br 2 (;@4;)
              end
              local.get 19
              i32.const 0
              call $store_checked_0
              local.get 19
              i32.const 1
              i32.add
              local.set 18
              local.get 19
              local.set 11
              br 0 (;@5;)
            end
          end
        end
        block ;; label = @3
          block ;; label = @4
            block ;; label = @5
              local.get 3
              i32.const 65546
              i32.gt_s
              br_if 0 (;@5;)
              i32.const 0
              local.set 12
              local.get 3
              i32.const 2113929216
              i32.gt_u
              br_if 2 (;@3;)
              block ;; label = @6
                local.get 3
                br_if 0 (;@6;)
                local.get 4
                i32.const 1
                i32.lt_s
                br_if 3 (;@3;)
                local.get 2
                i32.const 0
                call $store_checked_0
                i32.const 1
                return
              end
              local.get 7
              i32.const 3
              call $store_checked_1
              local.get 7
              local.get 7
              i32.const 16400
              i32.const 4
              call $readcheck
              i32.load offset=16400
              local.get 3
              i32.add
              call $store_checked_2
              local.get 7
              local.get 7
              i32.const 16392
              i32.const 4
              call $readcheck
              i32.load offset=16392
              local.tee 16
              local.get 3
              i32.add
              call $store_checked_3
              local.get 2
              local.get 4
              i32.add
              local.set 10
              local.get 1
              local.get 3
              i32.add
              local.set 9
              i32.const 0
              local.set 12
              block ;; label = @6
                local.get 3
                i32.const 13
                i32.ge_u
                br_if 0 (;@6;)
                local.get 2
                local.set 11
                local.get 1
                local.set 0
                br 2 (;@4;)
              end
              local.get 9
              i32.const -5
              i32.add
              local.set 15
              local.get 9
              i32.const -11
              i32.add
              local.set 13
              local.get 1
              local.get 16
              i32.sub
              local.set 18
              local.get 7
              local.get 1
              i32.const 0
              i32.const 4
              call $readcheck
              i32.load align=1
              i32.const -1640531535
              i32.mul
              i32.const 18
              i32.shr_u
              i32.const 16382
              i32.and
              i32.add
              local.get 16
              call $store_checked_4
              local.get 1
              i32.const 0
              local.get 16
              i32.sub
              i32.add
              local.set 22
              local.get 9
              i32.const -6
              i32.add
              local.set 23
              local.get 9
              i32.const -8
              i32.add
              local.set 6
              local.get 8
              i32.const 6
              i32.shl
              local.set 8
              local.get 2
              local.set 11
              local.get 1
              local.set 0
              loop ;; label = @6
                local.get 0
                i32.const 1
                i32.add
                local.set 3
                local.get 0
                i32.const 1
                i32.const 4
                call $readcheck
                i32.load offset=1 align=1
                local.set 5
                i32.const 1
                local.set 14
                local.get 8
                local.set 4
                loop ;; label = @7
                  local.get 3
                  local.tee 17
                  local.get 14
                  i32.add
                  local.tee 3
                  local.get 13
                  i32.gt_u
                  br_if 3 (;@4;)
                  local.get 7
                  local.get 5
                  i32.const -1640531535
                  i32.mul
                  i32.const 18
                  i32.shr_u
                  i32.const 16382
                  i32.and
                  i32.add
                  local.tee 14
                  i32.const 0
                  i32.const 2
                  call $readcheck
                  i32.load16_u
                  local.set 19
                  local.get 14
                  local.get 17
                  local.get 18
                  i32.sub
                  call $store_checked_4
                  local.get 4
                  i32.const 6
                  i32.shr_u
                  local.set 14
                  local.get 18
                  local.get 19
                  i32.add
                  local.tee 20
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load align=1
                  local.get 5
                  i32.ne
                  local.set 21
                  local.get 3
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load align=1
                  local.set 5
                  local.get 4
                  i32.const 1
                  i32.add
                  local.set 4
                  local.get 21
                  br_if 0 (;@7;)
                end
                block ;; label = @7
                  block ;; label = @8
                    local.get 19
                    local.get 16
                    i32.sub
                    i32.const 1
                    i32.lt_s
                    br_if 0 (;@8;)
                    local.get 17
                    i32.const -1
                    i32.add
                    local.tee 14
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    local.get 20
                    i32.const -1
                    i32.add
                    local.tee 5
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    i32.ne
                    br_if 0 (;@8;)
                    local.get 16
                    local.get 19
                    i32.sub
                    i32.const -2
                    i32.gt_s
                    br_if 1 (;@7;)
                    local.get 14
                    local.get 0
                    i32.le_u
                    br_if 1 (;@7;)
                    local.get 22
                    local.get 19
                    i32.add
                    local.set 19
                    i32.const 0
                    local.set 3
                    block ;; label = @9
                      block ;; label = @10
                        loop ;; label = @11
                          local.get 17
                          local.get 3
                          i32.add
                          local.tee 14
                          i32.const -2
                          i32.add
                          local.tee 4
                          i32.const 0
                          i32.const 1
                          call $readcheck
                          i32.load8_u
                          local.get 19
                          local.get 3
                          i32.add
                          local.tee 21
                          i32.const -2
                          i32.add
                          local.tee 5
                          i32.const 0
                          i32.const 1
                          call $readcheck
                          i32.load8_u
                          i32.ne
                          br_if 1 (;@10;)
                          local.get 3
                          i32.const -1
                          i32.add
                          local.set 3
                          local.get 5
                          local.get 1
                          i32.le_u
                          br_if 2 (;@9;)
                          local.get 4
                          local.get 0
                          i32.le_u
                          br_if 2 (;@9;)
                          br 0 (;@11;)
                        end
                      end
                      local.get 14
                      i32.const -1
                      i32.add
                      local.set 14
                      local.get 21
                      i32.const -1
                      i32.add
                      local.set 5
                      br 2 (;@7;)
                    end
                    local.get 17
                    local.get 3
                    i32.add
                    i32.const -1
                    i32.add
                    local.set 14
                    local.get 19
                    local.get 3
                    i32.add
                    i32.const -1
                    i32.add
                    local.set 5
                    br 1 (;@7;)
                  end
                  local.get 17
                  local.set 14
                  local.get 20
                  local.set 5
                end
                block ;; label = @7
                  local.get 11
                  i32.const 1
                  i32.add
                  local.tee 3
                  local.get 14
                  local.get 0
                  i32.sub
                  local.tee 17
                  i32.add
                  local.get 17
                  i32.const 255
                  i32.div_u
                  i32.add
                  i32.const 8
                  i32.add
                  local.get 10
                  i32.le_u
                  br_if 0 (;@7;)
                  i32.const 0
                  return
                end
                block ;; label = @7
                  block ;; label = @8
                    local.get 17
                    i32.const 15
                    i32.lt_u
                    br_if 0 (;@8;)
                    local.get 11
                    i32.const 240
                    call $store_checked_0
                    block ;; label = @9
                      local.get 17
                      i32.const -15
                      i32.add
                      local.tee 4
                      i32.const 255
                      i32.lt_u
                      br_if 0 (;@9;)
                      loop ;; label = @10
                        local.get 3
                        i32.const 255
                        call $store_checked_0
                        local.get 3
                        i32.const 1
                        i32.add
                        local.set 3
                        local.get 4
                        i32.const -255
                        i32.add
                        local.tee 4
                        i32.const 254
                        i32.gt_u
                        br_if 0 (;@10;)
                      end
                    end
                    local.get 3
                    local.get 4
                    call $store_checked_0
                    local.get 3
                    i32.const 1
                    i32.add
                    local.set 3
                    br 1 (;@7;)
                  end
                  local.get 11
                  local.get 17
                  i32.const 4
                  i32.shl
                  call $store_checked_0
                end
                local.get 3
                local.get 17
                i32.add
                local.set 19
                loop ;; label = @7
                  local.get 3
                  local.get 0
                  i32.const 8
                  call 3
                  drop
                  local.get 0
                  i32.const 8
                  i32.add
                  local.set 0
                  local.get 3
                  i32.const 8
                  i32.add
                  local.tee 3
                  local.get 19
                  i32.lt_u
                  br_if 0 (;@7;)
                end
                loop ;; label = @7
                  local.get 19
                  local.get 14
                  local.get 5
                  i32.sub
                  call $store_checked_5
                  local.get 5
                  i32.const 4
                  i32.add
                  local.set 3
                  block ;; label = @8
                    block ;; label = @9
                      block ;; label = @10
                        block ;; label = @11
                          local.get 14
                          i32.const 4
                          i32.add
                          local.tee 21
                          local.get 6
                          i32.lt_u
                          br_if 0 (;@11;)
                          local.get 21
                          local.set 0
                          br 1 (;@10;)
                        end
                        local.get 3
                        i32.const 0
                        i32.const 4
                        call $readcheck
                        i32.load align=1
                        local.tee 3
                        local.get 21
                        i32.const 0
                        i32.const 4
                        call $readcheck
                        i32.load align=1
                        local.tee 0
                        i32.ne
                        br_if 1 (;@9;)
                        local.get 5
                        i32.const 8
                        i32.add
                        local.set 3
                        local.get 14
                        i32.const 8
                        i32.add
                        local.set 0
                      end
                      block ;; label = @10
                        local.get 0
                        local.get 6
                        i32.ge_u
                        br_if 0 (;@10;)
                        local.get 0
                        local.get 14
                        i32.sub
                        i32.const -4
                        i32.add
                        local.set 5
                        loop ;; label = @11
                          block ;; label = @12
                            local.get 3
                            i32.const 0
                            i32.const 4
                            call $readcheck
                            i32.load align=1
                            local.tee 4
                            local.get 0
                            i32.const 0
                            i32.const 4
                            call $readcheck
                            i32.load align=1
                            local.tee 17
                            i32.eq
                            br_if 0 (;@12;)
                            local.get 17
                            local.get 4
                            i32.xor
                            i32.ctz
                            i32.const 3
                            i32.shr_u
                            local.get 5
                            i32.add
                            local.set 5
                            br 4 (;@8;)
                          end
                          local.get 5
                          i32.const 4
                          i32.add
                          local.set 5
                          local.get 3
                          i32.const 4
                          i32.add
                          local.set 3
                          local.get 0
                          i32.const 4
                          i32.add
                          local.tee 0
                          local.get 6
                          i32.lt_u
                          br_if 0 (;@11;)
                        end
                      end
                      block ;; label = @10
                        local.get 0
                        local.get 23
                        i32.ge_u
                        br_if 0 (;@10;)
                        local.get 3
                        i32.const 0
                        i32.const 2
                        call $readcheck
                        i32.load16_u align=1
                        local.get 0
                        i32.const 0
                        i32.const 2
                        call $readcheck
                        i32.load16_u align=1
                        i32.ne
                        br_if 0 (;@10;)
                        local.get 3
                        i32.const 2
                        i32.add
                        local.set 3
                        local.get 0
                        i32.const 2
                        i32.add
                        local.set 0
                      end
                      block ;; label = @10
                        local.get 0
                        local.get 15
                        i32.ge_u
                        br_if 0 (;@10;)
                        local.get 0
                        local.get 3
                        i32.const 0
                        i32.const 1
                        call $readcheck
                        i32.load8_u
                        local.get 0
                        i32.const 0
                        i32.const 1
                        call $readcheck
                        i32.load8_u
                        i32.eq
                        i32.add
                        local.set 0
                      end
                      local.get 0
                      local.get 21
                      i32.sub
                      local.set 5
                      br 1 (;@8;)
                    end
                    local.get 0
                    local.get 3
                    i32.xor
                    i32.ctz
                    i32.const 3
                    i32.shr_u
                    local.set 5
                  end
                  block ;; label = @8
                    local.get 19
                    local.get 5
                    i32.const 240
                    i32.add
                    i32.const 255
                    i32.div_u
                    i32.add
                    i32.const 8
                    i32.add
                    local.get 10
                    i32.le_u
                    br_if 0 (;@8;)
                    i32.const 0
                    return
                  end
                  local.get 19
                  i32.const 2
                  i32.add
                  local.set 3
                  local.get 14
                  local.get 5
                  i32.add
                  local.tee 4
                  i32.const 4
                  i32.add
                  local.set 14
                  local.get 11
                  i32.const 0
                  i32.const 1
                  call $readcheck
                  i32.load8_u
                  local.set 0
                  block ;; label = @8
                    block ;; label = @9
                      local.get 5
                      i32.const 15
                      i32.lt_u
                      br_if 0 (;@9;)
                      local.get 11
                      local.get 0
                      i32.const 15
                      i32.add
                      call $store_checked_0
                      local.get 3
                      i32.const -1
                      call $store_checked_6
                      block ;; label = @10
                        local.get 5
                        i32.const -15
                        i32.add
                        local.tee 0
                        i32.const 1020
                        i32.lt_u
                        br_if 0 (;@10;)
                        block ;; label = @11
                          local.get 5
                          i32.const -1035
                          i32.add
                          local.tee 17
                          i32.const 1020
                          i32.div_u
                          i32.const 1
                          i32.add
                          i32.const 7
                          i32.and
                          local.tee 5
                          i32.eqz
                          br_if 0 (;@11;)
                          local.get 19
                          i32.const 6
                          i32.add
                          local.set 3
                          loop ;; label = @12
                            local.get 3
                            i32.const -1
                            call $store_checked_6
                            local.get 3
                            i32.const 4
                            i32.add
                            local.set 3
                            local.get 0
                            i32.const -1020
                            i32.add
                            local.set 0
                            local.get 5
                            i32.const -1
                            i32.add
                            local.tee 5
                            br_if 0 (;@12;)
                          end
                          local.get 3
                          i32.const -4
                          i32.add
                          local.set 3
                        end
                        local.get 17
                        i32.const 7140
                        i32.lt_u
                        br_if 0 (;@10;)
                        loop ;; label = @11
                          local.get 3
                          i32.const 28
                          i32.add
                          i64.const -1
                          i64.store align=1
                          local.get 3
                          i32.const 20
                          i32.add
                          i64.const -1
                          i64.store align=1
                          local.get 3
                          i32.const 12
                          i32.add
                          i64.const -1
                          i64.store align=1
                          local.get 3
                          i32.const 4
                          i32.add
                          i64.const -1
                          i64.store align=1
                          local.get 3
                          i32.const 32
                          i32.add
                          local.set 3
                          local.get 0
                          i32.const -8160
                          i32.add
                          local.tee 0
                          i32.const 1019
                          i32.gt_u
                          br_if 0 (;@11;)
                        end
                      end
                      local.get 3
                      local.get 0
                      i32.const 65535
                      i32.and
                      i32.const 255
                      i32.div_u
                      local.tee 5
                      i32.add
                      local.tee 3
                      local.get 0
                      local.get 5
                      i32.add
                      call $store_checked_0
                      local.get 3
                      i32.const 1
                      i32.add
                      local.set 3
                      br 1 (;@8;)
                    end
                    local.get 11
                    local.get 0
                    local.get 5
                    i32.add
                    call $store_checked_0
                  end
                  block ;; label = @8
                    local.get 14
                    local.get 13
                    i32.lt_u
                    br_if 0 (;@8;)
                    local.get 3
                    local.set 11
                    local.get 14
                    local.set 0
                    br 4 (;@4;)
                  end
                  local.get 7
                  local.get 4
                  i32.const 2
                  i32.add
                  local.tee 0
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load align=1
                  i32.const -1640531535
                  i32.mul
                  i32.const 18
                  i32.shr_u
                  i32.const 16382
                  i32.and
                  i32.add
                  local.get 0
                  local.get 18
                  i32.sub
                  call $store_checked_4
                  local.get 7
                  local.get 14
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load align=1
                  local.tee 0
                  i32.const -1640531535
                  i32.mul
                  i32.const 18
                  i32.shr_u
                  i32.const 16382
                  i32.and
                  i32.add
                  local.tee 5
                  i32.const 0
                  i32.const 2
                  call $readcheck
                  i32.load16_u
                  local.set 4
                  local.get 5
                  local.get 14
                  local.get 18
                  i32.sub
                  call $store_checked_4
                  block ;; label = @8
                    local.get 0
                    local.get 18
                    local.get 4
                    i32.add
                    local.tee 5
                    i32.const 0
                    i32.const 4
                    call $readcheck
                    i32.load align=1
                    i32.eq
                    br_if 0 (;@8;)
                    local.get 3
                    local.set 11
                    local.get 14
                    local.set 0
                    br 2 (;@6;)
                  end
                  local.get 3
                  i32.const 0
                  call $store_checked_0
                  local.get 3
                  i32.const 1
                  i32.add
                  local.set 19
                  local.get 3
                  local.set 11
                  br 0 (;@7;)
                end
              end
            end
            block ;; label = @5
              local.get 3
              i32.const 2113929216
              i32.le_u
              br_if 0 (;@5;)
              i32.const 0
              return
            end
            local.get 7
            local.get 7
            i32.const 16400
            i32.const 4
            call $readcheck
            i32.load offset=16400
            local.get 3
            i32.add
            call $store_checked_2
            local.get 7
            i32.const 1
            i32.const 2
            local.get 1
            i32.const 65535
            i32.gt_u
            local.tee 5
            select
            call $store_checked_1
            local.get 7
            local.get 7
            i32.const 16392
            i32.const 4
            call $readcheck
            i32.load offset=16392
            local.tee 0
            local.get 3
            i32.add
            call $store_checked_3
            local.get 7
            local.get 1
            i32.const 0
            i32.const 4
            call $readcheck
            i32.load align=1
            i32.const -1640531535
            i32.mul
            i32.const 18
            i32.shr_u
            i32.const 16380
            i32.and
            i32.add
            local.get 1
            local.get 0
            local.get 5
            select
            call $store_checked_7
            local.get 2
            local.get 4
            i32.add
            local.set 10
            local.get 1
            local.get 3
            i32.add
            local.tee 16
            i32.const -6
            i32.add
            local.set 23
            local.get 16
            i32.const -8
            i32.add
            local.set 6
            local.get 8
            i32.const 6
            i32.shl
            i32.const 1
            i32.or
            local.set 15
            local.get 16
            i32.const -5
            i32.add
            local.set 22
            local.get 16
            i32.const -11
            i32.add
            local.set 19
            local.get 1
            local.get 0
            i32.sub
            local.set 21
            local.get 1
            i32.const 65536
            i32.lt_u
            local.set 9
            local.get 2
            local.set 20
            local.get 1
            local.set 4
            block ;; label = @5
              loop ;; label = @6
                local.get 4
                i32.const 2
                i32.add
                local.set 0
                local.get 4
                i32.const 1
                i32.add
                local.set 3
                local.get 4
                i32.const 1
                i32.const 4
                call $readcheck
                i32.load offset=1 align=1
                i32.const -1640531535
                i32.mul
                i32.const 20
                i32.shr_u
                local.set 5
                block ;; label = @7
                  block ;; label = @8
                    local.get 9
                    br_if 0 (;@8;)
                    local.get 0
                    local.get 19
                    i32.gt_u
                    br_if 3 (;@5;)
                    local.get 8
                    local.set 18
                    local.get 15
                    local.set 17
                    loop ;; label = @9
                      local.get 7
                      local.get 5
                      i32.const 2
                      i32.shl
                      i32.add
                      local.tee 14
                      i32.const 0
                      i32.const 4
                      call $readcheck
                      i32.load
                      local.set 5
                      local.get 14
                      local.get 3
                      call $store_checked_7
                      local.get 0
                      local.tee 14
                      i32.const 0
                      i32.const 4
                      call $readcheck
                      i32.load align=1
                      local.set 0
                      block ;; label = @10
                        local.get 5
                        i32.const 65535
                        i32.add
                        local.get 3
                        i32.lt_u
                        br_if 0 (;@10;)
                        local.get 5
                        i32.const 0
                        i32.const 4
                        call $readcheck
                        i32.load align=1
                        local.get 3
                        i32.const 0
                        i32.const 4
                        call $readcheck
                        i32.load align=1
                        i32.eq
                        br_if 3 (;@7;)
                      end
                      local.get 0
                      i32.const -1640531535
                      i32.mul
                      i32.const 20
                      i32.shr_u
                      local.set 5
                      local.get 17
                      i32.const 6
                      i32.shr_u
                      local.set 3
                      local.get 17
                      i32.const 1
                      i32.add
                      local.set 17
                      local.get 14
                      local.get 18
                      i32.add
                      local.set 0
                      local.get 3
                      local.set 18
                      local.get 14
                      local.set 3
                      local.get 0
                      local.get 19
                      i32.le_u
                      br_if 0 (;@9;)
                      br 4 (;@5;)
                    end
                  end
                  local.get 0
                  local.get 19
                  i32.gt_u
                  br_if 2 (;@5;)
                  local.get 8
                  local.set 11
                  local.get 15
                  local.set 17
                  loop ;; label = @8
                    local.get 7
                    local.get 5
                    i32.const 2
                    i32.shl
                    i32.add
                    local.tee 18
                    i32.const 0
                    i32.const 4
                    call $readcheck
                    i32.load
                    local.set 5
                    local.get 0
                    local.tee 14
                    i32.const 0
                    i32.const 4
                    call $readcheck
                    i32.load align=1
                    local.set 13
                    local.get 18
                    local.get 3
                    local.get 21
                    i32.sub
                    local.tee 0
                    call $store_checked_7
                    block ;; label = @9
                      local.get 5
                      i32.const 65535
                      i32.add
                      local.get 0
                      i32.lt_u
                      br_if 0 (;@9;)
                      local.get 21
                      local.get 5
                      i32.add
                      local.tee 5
                      i32.const 0
                      i32.const 4
                      call $readcheck
                      i32.load align=1
                      local.get 3
                      i32.const 0
                      i32.const 4
                      call $readcheck
                      i32.load align=1
                      i32.eq
                      br_if 2 (;@7;)
                    end
                    local.get 13
                    i32.const -1640531535
                    i32.mul
                    i32.const 20
                    i32.shr_u
                    local.set 5
                    local.get 17
                    i32.const 6
                    i32.shr_u
                    local.set 3
                    local.get 17
                    i32.const 1
                    i32.add
                    local.set 17
                    local.get 14
                    local.get 11
                    i32.add
                    local.set 0
                    local.get 3
                    local.set 11
                    local.get 14
                    local.set 3
                    local.get 0
                    local.get 19
                    i32.le_u
                    br_if 0 (;@8;)
                    br 3 (;@5;)
                  end
                end
                block ;; label = @7
                  block ;; label = @8
                    local.get 5
                    local.get 1
                    i32.le_u
                    br_if 0 (;@8;)
                    local.get 3
                    i32.const -1
                    i32.add
                    local.tee 14
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    local.get 5
                    i32.const -1
                    i32.add
                    local.tee 0
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    i32.ne
                    br_if 0 (;@8;)
                    local.get 0
                    local.get 1
                    i32.le_u
                    br_if 1 (;@7;)
                    local.get 14
                    local.get 4
                    i32.le_u
                    br_if 1 (;@7;)
                    local.get 3
                    i32.const -2
                    i32.add
                    local.set 0
                    local.get 5
                    i32.const -2
                    i32.add
                    local.set 3
                    block ;; label = @9
                      block ;; label = @10
                        loop ;; label = @11
                          local.get 0
                          i32.const 0
                          i32.const 1
                          call $readcheck
                          i32.load8_u
                          local.get 3
                          i32.const 0
                          i32.const 1
                          call $readcheck
                          i32.load8_u
                          i32.ne
                          br_if 1 (;@10;)
                          local.get 0
                          i32.const -1
                          i32.add
                          local.set 5
                          local.get 3
                          i32.const -1
                          i32.add
                          local.set 17
                          local.get 3
                          local.get 1
                          i32.le_u
                          br_if 2 (;@9;)
                          local.get 0
                          local.get 4
                          i32.le_u
                          local.set 14
                          local.get 5
                          local.set 0
                          local.get 17
                          local.set 3
                          local.get 14
                          br_if 2 (;@9;)
                          br 0 (;@11;)
                        end
                      end
                      local.get 0
                      i32.const 1
                      i32.add
                      local.set 14
                      local.get 3
                      i32.const 1
                      i32.add
                      local.set 0
                      br 2 (;@7;)
                    end
                    local.get 5
                    i32.const 1
                    i32.add
                    local.set 14
                    local.get 17
                    i32.const 1
                    i32.add
                    local.set 0
                    br 1 (;@7;)
                  end
                  local.get 5
                  local.set 0
                  local.get 3
                  local.set 14
                end
                i32.const 0
                local.set 12
                local.get 20
                i32.const 1
                i32.add
                local.tee 3
                local.get 14
                local.get 4
                i32.sub
                local.tee 17
                i32.add
                local.get 17
                i32.const 255
                i32.div_u
                i32.add
                i32.const 8
                i32.add
                local.get 10
                i32.gt_u
                br_if 3 (;@3;)
                block ;; label = @7
                  block ;; label = @8
                    local.get 17
                    i32.const 15
                    i32.lt_u
                    br_if 0 (;@8;)
                    local.get 20
                    i32.const 240
                    call $store_checked_0
                    block ;; label = @9
                      local.get 17
                      i32.const -15
                      i32.add
                      local.tee 5
                      i32.const 255
                      i32.lt_u
                      br_if 0 (;@9;)
                      loop ;; label = @10
                        local.get 3
                        i32.const 255
                        call $store_checked_0
                        local.get 3
                        i32.const 1
                        i32.add
                        local.set 3
                        local.get 5
                        i32.const -255
                        i32.add
                        local.tee 5
                        i32.const 254
                        i32.gt_u
                        br_if 0 (;@10;)
                      end
                    end
                    local.get 3
                    local.get 5
                    call $store_checked_0
                    local.get 3
                    i32.const 1
                    i32.add
                    local.set 3
                    br 1 (;@7;)
                  end
                  local.get 20
                  local.get 17
                  i32.const 4
                  i32.shl
                  call $store_checked_0
                end
                local.get 3
                local.get 17
                i32.add
                local.set 18
                loop ;; label = @7
                  local.get 3
                  local.get 4
                  i32.const 8
                  call 3
                  drop
                  local.get 4
                  i32.const 8
                  i32.add
                  local.set 4
                  local.get 3
                  i32.const 8
                  i32.add
                  local.tee 3
                  local.get 18
                  i32.lt_u
                  br_if 0 (;@7;)
                end
                loop ;; label = @7
                  local.get 18
                  local.get 14
                  local.get 0
                  i32.sub
                  call $store_checked_5
                  local.get 0
                  i32.const 4
                  i32.add
                  local.set 3
                  block ;; label = @8
                    block ;; label = @9
                      block ;; label = @10
                        block ;; label = @11
                          local.get 14
                          i32.const 4
                          i32.add
                          local.tee 11
                          local.get 6
                          i32.lt_u
                          br_if 0 (;@11;)
                          local.get 11
                          local.set 0
                          br 1 (;@10;)
                        end
                        local.get 3
                        i32.const 0
                        i32.const 4
                        call $readcheck
                        i32.load align=1
                        local.tee 3
                        local.get 11
                        i32.const 0
                        i32.const 4
                        call $readcheck
                        i32.load align=1
                        local.tee 5
                        i32.ne
                        br_if 1 (;@9;)
                        local.get 0
                        i32.const 8
                        i32.add
                        local.set 3
                        local.get 14
                        i32.const 8
                        i32.add
                        local.set 0
                      end
                      block ;; label = @10
                        local.get 0
                        local.get 6
                        i32.ge_u
                        br_if 0 (;@10;)
                        local.get 0
                        local.get 14
                        i32.sub
                        i32.const -4
                        i32.add
                        local.set 5
                        loop ;; label = @11
                          block ;; label = @12
                            local.get 3
                            i32.const 0
                            i32.const 4
                            call $readcheck
                            i32.load align=1
                            local.tee 4
                            local.get 0
                            i32.const 0
                            i32.const 4
                            call $readcheck
                            i32.load align=1
                            local.tee 17
                            i32.eq
                            br_if 0 (;@12;)
                            local.get 17
                            local.get 4
                            i32.xor
                            i32.ctz
                            i32.const 3
                            i32.shr_u
                            local.get 5
                            i32.add
                            local.set 5
                            br 4 (;@8;)
                          end
                          local.get 5
                          i32.const 4
                          i32.add
                          local.set 5
                          local.get 3
                          i32.const 4
                          i32.add
                          local.set 3
                          local.get 0
                          i32.const 4
                          i32.add
                          local.tee 0
                          local.get 6
                          i32.lt_u
                          br_if 0 (;@11;)
                        end
                      end
                      block ;; label = @10
                        local.get 0
                        local.get 23
                        i32.ge_u
                        br_if 0 (;@10;)
                        local.get 3
                        i32.const 0
                        i32.const 2
                        call $readcheck
                        i32.load16_u align=1
                        local.get 0
                        i32.const 0
                        i32.const 2
                        call $readcheck
                        i32.load16_u align=1
                        i32.ne
                        br_if 0 (;@10;)
                        local.get 3
                        i32.const 2
                        i32.add
                        local.set 3
                        local.get 0
                        i32.const 2
                        i32.add
                        local.set 0
                      end
                      block ;; label = @10
                        local.get 0
                        local.get 22
                        i32.ge_u
                        br_if 0 (;@10;)
                        local.get 0
                        local.get 3
                        i32.const 0
                        i32.const 1
                        call $readcheck
                        i32.load8_u
                        local.get 0
                        i32.const 0
                        i32.const 1
                        call $readcheck
                        i32.load8_u
                        i32.eq
                        i32.add
                        local.set 0
                      end
                      local.get 0
                      local.get 11
                      i32.sub
                      local.set 5
                      br 1 (;@8;)
                    end
                    local.get 5
                    local.get 3
                    i32.xor
                    i32.ctz
                    i32.const 3
                    i32.shr_u
                    local.set 5
                  end
                  local.get 18
                  local.get 5
                  i32.const 240
                  i32.add
                  i32.const 255
                  i32.div_u
                  i32.add
                  i32.const 8
                  i32.add
                  local.get 10
                  i32.gt_u
                  br_if 4 (;@3;)
                  local.get 18
                  i32.const 2
                  i32.add
                  local.set 3
                  local.get 14
                  local.get 5
                  i32.add
                  local.tee 4
                  i32.const 4
                  i32.add
                  local.set 14
                  local.get 20
                  i32.const 0
                  i32.const 1
                  call $readcheck
                  i32.load8_u
                  local.set 0
                  block ;; label = @8
                    block ;; label = @9
                      local.get 5
                      i32.const 15
                      i32.lt_u
                      br_if 0 (;@9;)
                      local.get 20
                      local.get 0
                      i32.const 15
                      i32.add
                      call $store_checked_0
                      local.get 3
                      i32.const -1
                      call $store_checked_6
                      block ;; label = @10
                        local.get 5
                        i32.const -15
                        i32.add
                        local.tee 0
                        i32.const 1020
                        i32.lt_u
                        br_if 0 (;@10;)
                        block ;; label = @11
                          local.get 5
                          i32.const -1035
                          i32.add
                          local.tee 17
                          i32.const 1020
                          i32.div_u
                          i32.const 1
                          i32.add
                          i32.const 7
                          i32.and
                          local.tee 5
                          i32.eqz
                          br_if 0 (;@11;)
                          local.get 18
                          i32.const 6
                          i32.add
                          local.set 3
                          loop ;; label = @12
                            local.get 3
                            i32.const -1
                            call $store_checked_6
                            local.get 3
                            i32.const 4
                            i32.add
                            local.set 3
                            local.get 0
                            i32.const -1020
                            i32.add
                            local.set 0
                            local.get 5
                            i32.const -1
                            i32.add
                            local.tee 5
                            br_if 0 (;@12;)
                          end
                          local.get 3
                          i32.const -4
                          i32.add
                          local.set 3
                        end
                        local.get 17
                        i32.const 7140
                        i32.lt_u
                        br_if 0 (;@10;)
                        loop ;; label = @11
                          local.get 3
                          i32.const 28
                          i32.add
                          i64.const -1
                          i64.store align=1
                          local.get 3
                          i32.const 20
                          i32.add
                          i64.const -1
                          i64.store align=1
                          local.get 3
                          i32.const 12
                          i32.add
                          i64.const -1
                          i64.store align=1
                          local.get 3
                          i32.const 4
                          i32.add
                          i64.const -1
                          i64.store align=1
                          local.get 3
                          i32.const 32
                          i32.add
                          local.set 3
                          local.get 0
                          i32.const -8160
                          i32.add
                          local.tee 0
                          i32.const 1019
                          i32.gt_u
                          br_if 0 (;@11;)
                        end
                      end
                      local.get 3
                      local.get 0
                      i32.const 65535
                      i32.and
                      i32.const 255
                      i32.div_u
                      local.tee 5
                      i32.add
                      local.tee 3
                      local.get 0
                      local.get 5
                      i32.add
                      call $store_checked_0
                      local.get 3
                      i32.const 1
                      i32.add
                      local.set 20
                      br 1 (;@8;)
                    end
                    local.get 20
                    local.get 0
                    local.get 5
                    i32.add
                    call $store_checked_0
                    local.get 3
                    local.set 20
                  end
                  block ;; label = @8
                    local.get 14
                    local.get 19
                    i32.lt_u
                    br_if 0 (;@8;)
                    local.get 14
                    local.set 4
                    br 3 (;@5;)
                  end
                  local.get 4
                  i32.const 2
                  i32.add
                  local.tee 3
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load align=1
                  i32.const -1640531535
                  i32.mul
                  i32.const 20
                  i32.shr_u
                  local.set 0
                  block ;; label = @8
                    block ;; label = @9
                      local.get 9
                      br_if 0 (;@9;)
                      local.get 7
                      local.get 0
                      i32.const 2
                      i32.shl
                      i32.add
                      local.get 3
                      call $store_checked_7
                      local.get 7
                      local.get 14
                      i32.const 0
                      i32.const 4
                      call $readcheck
                      i32.load align=1
                      local.tee 5
                      i32.const -1640531535
                      i32.mul
                      i32.const 18
                      i32.shr_u
                      i32.const 16380
                      i32.and
                      i32.add
                      local.tee 3
                      i32.const 0
                      i32.const 4
                      call $readcheck
                      i32.load
                      local.set 0
                      local.get 3
                      local.get 14
                      call $store_checked_7
                      block ;; label = @10
                        local.get 0
                        i32.const 65535
                        i32.add
                        local.get 14
                        i32.ge_u
                        br_if 0 (;@10;)
                        local.get 14
                        local.set 4
                        br 4 (;@6;)
                      end
                      local.get 0
                      i32.const 0
                      i32.const 4
                      call $readcheck
                      i32.load align=1
                      local.get 5
                      i32.eq
                      br_if 1 (;@8;)
                      local.get 14
                      local.set 4
                      br 3 (;@6;)
                    end
                    local.get 7
                    local.get 0
                    i32.const 2
                    i32.shl
                    i32.add
                    local.get 3
                    local.get 21
                    i32.sub
                    call $store_checked_7
                    local.get 7
                    local.get 14
                    i32.const 0
                    i32.const 4
                    call $readcheck
                    i32.load align=1
                    i32.const -1640531535
                    i32.mul
                    i32.const 18
                    i32.shr_u
                    i32.const 16380
                    i32.and
                    i32.add
                    local.tee 0
                    i32.const 0
                    i32.const 4
                    call $readcheck
                    i32.load
                    local.set 3
                    local.get 0
                    local.get 14
                    local.get 21
                    i32.sub
                    local.tee 5
                    call $store_checked_7
                    block ;; label = @9
                      local.get 3
                      i32.const 65535
                      i32.add
                      local.get 5
                      i32.ge_u
                      br_if 0 (;@9;)
                      local.get 14
                      local.set 4
                      br 3 (;@6;)
                    end
                    local.get 21
                    local.get 3
                    i32.add
                    local.tee 0
                    i32.const 0
                    i32.const 4
                    call $readcheck
                    i32.load align=1
                    local.get 14
                    i32.const 0
                    i32.const 4
                    call $readcheck
                    i32.load align=1
                    i32.eq
                    br_if 0 (;@8;)
                    local.get 14
                    local.set 4
                    br 2 (;@6;)
                  end
                  local.get 20
                  i32.const 0
                  call $store_checked_0
                  local.get 20
                  i32.const 1
                  i32.add
                  local.set 18
                  br 0 (;@7;)
                end
              end
            end
            block ;; label = @5
              local.get 20
              local.get 16
              local.get 4
              i32.sub
              local.tee 5
              i32.add
              local.get 5
              i32.const 240
              i32.add
              i32.const 255
              i32.div_u
              i32.add
              i32.const 1
              i32.add
              local.get 10
              i32.le_u
              br_if 0 (;@5;)
              i32.const 0
              return
            end
            local.get 20
            i32.const 1
            i32.add
            local.set 3
            block ;; label = @5
              block ;; label = @6
                local.get 5
                i32.const 15
                i32.lt_u
                br_if 0 (;@6;)
                local.get 20
                i32.const 240
                call $store_checked_0
                block ;; label = @7
                  local.get 5
                  i32.const -15
                  i32.add
                  local.tee 0
                  i32.const 255
                  i32.lt_u
                  br_if 0 (;@7;)
                  loop ;; label = @8
                    local.get 3
                    i32.const 255
                    call $store_checked_0
                    local.get 3
                    i32.const 1
                    i32.add
                    local.set 3
                    local.get 0
                    i32.const -255
                    i32.add
                    local.tee 0
                    i32.const 254
                    i32.gt_u
                    br_if 0 (;@8;)
                  end
                  local.get 3
                  i32.const -1
                  i32.add
                  local.set 20
                end
                local.get 3
                local.get 0
                call $store_checked_0
                local.get 20
                i32.const 2
                i32.add
                local.set 3
                br 1 (;@5;)
              end
              local.get 20
              local.get 5
              i32.const 4
              i32.shl
              call $store_checked_0
            end
            local.get 3
            local.get 4
            local.get 5
            call 3
            drop
            local.get 3
            local.get 5
            i32.add
            local.get 2
            i32.sub
            local.set 12
            br 1 (;@3;)
          end
          local.get 11
          local.get 9
          local.get 0
          i32.sub
          local.tee 7
          i32.add
          local.get 7
          i32.const 240
          i32.add
          i32.const 255
          i32.div_u
          i32.add
          i32.const 1
          i32.add
          local.get 10
          i32.gt_u
          br_if 0 (;@3;)
          local.get 11
          i32.const 1
          i32.add
          local.set 3
          block ;; label = @4
            block ;; label = @5
              local.get 7
              i32.const 15
              i32.lt_u
              br_if 0 (;@5;)
              local.get 11
              i32.const 240
              call $store_checked_0
              block ;; label = @6
                local.get 7
                i32.const -15
                i32.add
                local.tee 5
                i32.const 255
                i32.lt_u
                br_if 0 (;@6;)
                loop ;; label = @7
                  local.get 3
                  i32.const 255
                  call $store_checked_0
                  local.get 3
                  i32.const 1
                  i32.add
                  local.set 3
                  local.get 5
                  i32.const -255
                  i32.add
                  local.tee 5
                  i32.const 254
                  i32.gt_u
                  br_if 0 (;@7;)
                end
                local.get 3
                i32.const -1
                i32.add
                local.set 11
              end
              local.get 3
              local.get 5
              call $store_checked_0
              local.get 11
              i32.const 2
              i32.add
              local.set 3
              br 1 (;@4;)
            end
            local.get 11
            local.get 7
            i32.const 4
            i32.shl
            call $store_checked_0
          end
          local.get 3
          local.get 0
          local.get 7
          call 3
          drop
          local.get 3
          local.get 7
          i32.add
          local.get 2
          i32.sub
          return
        end
        local.get 12
        return
      end
      block ;; label = @2
        local.get 3
        i32.const 2113929216
        i32.le_u
        br_if 0 (;@2;)
        i32.const 0
        return
      end
      local.get 7
      local.get 7
      i32.const 16400
      i32.const 4
      call $readcheck
      i32.load offset=16400
      local.get 3
      i32.add
      call $store_checked_2
      local.get 7
      i32.const 1
      i32.const 2
      local.get 1
      i32.const 65535
      i32.gt_u
      local.tee 5
      select
      call $store_checked_1
      local.get 7
      local.get 7
      i32.const 16392
      i32.const 4
      call $readcheck
      i32.load offset=16392
      local.tee 0
      local.get 3
      i32.add
      call $store_checked_3
      local.get 7
      local.get 1
      i32.const 0
      i32.const 4
      call $readcheck
      i32.load align=1
      i32.const -1640531535
      i32.mul
      i32.const 18
      i32.shr_u
      i32.const 16380
      i32.and
      i32.add
      local.get 1
      local.get 0
      local.get 5
      select
      call $store_checked_7
      local.get 1
      local.get 3
      i32.add
      local.tee 9
      i32.const -6
      i32.add
      local.set 16
      local.get 9
      i32.const -8
      i32.add
      local.set 5
      local.get 8
      i32.const 6
      i32.shl
      i32.const 1
      i32.or
      local.set 12
      local.get 9
      i32.const -5
      i32.add
      local.set 15
      local.get 9
      i32.const -11
      i32.add
      local.set 18
      local.get 1
      local.get 0
      i32.sub
      local.set 19
      local.get 1
      i32.const 65536
      i32.lt_u
      local.set 10
      local.get 2
      local.set 20
      local.get 1
      local.set 4
      block ;; label = @2
        loop ;; label = @3
          local.get 4
          i32.const 2
          i32.add
          local.set 0
          local.get 4
          i32.const 1
          i32.add
          local.set 3
          local.get 4
          i32.const 1
          i32.const 4
          call $readcheck
          i32.load offset=1 align=1
          i32.const -1640531535
          i32.mul
          i32.const 20
          i32.shr_u
          local.set 6
          block ;; label = @4
            block ;; label = @5
              local.get 10
              br_if 0 (;@5;)
              local.get 0
              local.get 18
              i32.gt_u
              br_if 3 (;@2;)
              local.get 8
              local.set 21
              local.get 12
              local.set 17
              loop ;; label = @6
                local.get 7
                local.get 6
                i32.const 2
                i32.shl
                i32.add
                local.tee 14
                i32.const 0
                i32.const 4
                call $readcheck
                i32.load
                local.set 6
                local.get 14
                local.get 3
                call $store_checked_7
                local.get 0
                local.tee 14
                i32.const 0
                i32.const 4
                call $readcheck
                i32.load align=1
                local.set 0
                block ;; label = @7
                  local.get 6
                  i32.const 65535
                  i32.add
                  local.get 3
                  i32.lt_u
                  br_if 0 (;@7;)
                  local.get 6
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load align=1
                  local.get 3
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load align=1
                  i32.eq
                  br_if 3 (;@4;)
                end
                local.get 0
                i32.const -1640531535
                i32.mul
                i32.const 20
                i32.shr_u
                local.set 6
                local.get 17
                i32.const 6
                i32.shr_u
                local.set 3
                local.get 17
                i32.const 1
                i32.add
                local.set 17
                local.get 14
                local.get 21
                i32.add
                local.set 0
                local.get 3
                local.set 21
                local.get 14
                local.set 3
                local.get 0
                local.get 18
                i32.le_u
                br_if 0 (;@6;)
                br 4 (;@2;)
              end
            end
            local.get 0
            local.get 18
            i32.gt_u
            br_if 2 (;@2;)
            local.get 8
            local.set 11
            local.get 12
            local.set 17
            loop ;; label = @5
              local.get 7
              local.get 6
              i32.const 2
              i32.shl
              i32.add
              local.tee 21
              i32.const 0
              i32.const 4
              call $readcheck
              i32.load
              local.set 6
              local.get 0
              local.tee 14
              i32.const 0
              i32.const 4
              call $readcheck
              i32.load align=1
              local.set 13
              local.get 21
              local.get 3
              local.get 19
              i32.sub
              local.tee 0
              call $store_checked_7
              block ;; label = @6
                local.get 6
                i32.const 65535
                i32.add
                local.get 0
                i32.lt_u
                br_if 0 (;@6;)
                local.get 19
                local.get 6
                i32.add
                local.tee 6
                i32.const 0
                i32.const 4
                call $readcheck
                i32.load align=1
                local.get 3
                i32.const 0
                i32.const 4
                call $readcheck
                i32.load align=1
                i32.eq
                br_if 2 (;@4;)
              end
              local.get 13
              i32.const -1640531535
              i32.mul
              i32.const 20
              i32.shr_u
              local.set 6
              local.get 17
              i32.const 6
              i32.shr_u
              local.set 3
              local.get 17
              i32.const 1
              i32.add
              local.set 17
              local.get 14
              local.get 11
              i32.add
              local.set 0
              local.get 3
              local.set 11
              local.get 14
              local.set 3
              local.get 0
              local.get 18
              i32.le_u
              br_if 0 (;@5;)
              br 3 (;@2;)
            end
          end
          block ;; label = @4
            block ;; label = @5
              local.get 6
              local.get 1
              i32.le_u
              br_if 0 (;@5;)
              local.get 3
              i32.const -1
              i32.add
              local.tee 17
              i32.const 0
              i32.const 1
              call $readcheck
              i32.load8_u
              local.get 6
              i32.const -1
              i32.add
              local.tee 11
              i32.const 0
              i32.const 1
              call $readcheck
              i32.load8_u
              i32.ne
              br_if 0 (;@5;)
              local.get 11
              local.get 1
              i32.le_u
              br_if 1 (;@4;)
              local.get 17
              local.get 4
              i32.le_u
              br_if 1 (;@4;)
              local.get 3
              i32.const -2
              i32.add
              local.set 0
              local.get 6
              i32.const -2
              i32.add
              local.set 3
              block ;; label = @6
                block ;; label = @7
                  loop ;; label = @8
                    local.get 0
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    local.get 3
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    i32.ne
                    br_if 1 (;@7;)
                    local.get 0
                    i32.const -1
                    i32.add
                    local.set 6
                    local.get 3
                    i32.const -1
                    i32.add
                    local.set 14
                    local.get 3
                    local.get 1
                    i32.le_u
                    br_if 2 (;@6;)
                    local.get 0
                    local.get 4
                    i32.le_u
                    local.set 17
                    local.get 6
                    local.set 0
                    local.get 14
                    local.set 3
                    local.get 17
                    br_if 2 (;@6;)
                    br 0 (;@8;)
                  end
                end
                local.get 0
                i32.const 1
                i32.add
                local.set 17
                local.get 3
                i32.const 1
                i32.add
                local.set 11
                br 2 (;@4;)
              end
              local.get 6
              i32.const 1
              i32.add
              local.set 17
              local.get 14
              i32.const 1
              i32.add
              local.set 11
              br 1 (;@4;)
            end
            local.get 6
            local.set 11
            local.get 3
            local.set 17
          end
          local.get 20
          i32.const 1
          i32.add
          local.set 3
          block ;; label = @4
            block ;; label = @5
              local.get 17
              local.get 4
              i32.sub
              local.tee 6
              i32.const 15
              i32.lt_u
              br_if 0 (;@5;)
              local.get 20
              i32.const 240
              call $store_checked_0
              block ;; label = @6
                local.get 6
                i32.const -15
                i32.add
                local.tee 0
                i32.const 255
                i32.lt_u
                br_if 0 (;@6;)
                loop ;; label = @7
                  local.get 3
                  i32.const 255
                  call $store_checked_0
                  local.get 3
                  i32.const 1
                  i32.add
                  local.set 3
                  local.get 0
                  i32.const -255
                  i32.add
                  local.tee 0
                  i32.const 254
                  i32.gt_u
                  br_if 0 (;@7;)
                end
              end
              local.get 3
              local.get 0
              call $store_checked_0
              local.get 3
              i32.const 1
              i32.add
              local.set 3
              br 1 (;@4;)
            end
            local.get 20
            local.get 6
            i32.const 4
            i32.shl
            call $store_checked_0
          end
          local.get 3
          local.get 6
          i32.add
          local.set 14
          loop ;; label = @4
            local.get 3
            local.get 4
            i32.const 8
            call 3
            drop
            local.get 4
            i32.const 8
            i32.add
            local.set 4
            local.get 3
            i32.const 8
            i32.add
            local.tee 3
            local.get 14
            i32.lt_u
            br_if 0 (;@4;)
          end
          loop ;; label = @4
            local.get 14
            local.get 17
            local.get 11
            i32.sub
            call $store_checked_5
            local.get 11
            i32.const 4
            i32.add
            local.set 0
            local.get 14
            i32.const 2
            i32.add
            local.set 21
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    block ;; label = @9
                      local.get 17
                      i32.const 4
                      i32.add
                      local.tee 13
                      local.get 5
                      i32.lt_u
                      br_if 0 (;@9;)
                      local.get 13
                      local.set 3
                      br 1 (;@8;)
                    end
                    local.get 0
                    i32.const 0
                    i32.const 4
                    call $readcheck
                    i32.load align=1
                    local.tee 3
                    local.get 13
                    i32.const 0
                    i32.const 4
                    call $readcheck
                    i32.load align=1
                    local.tee 0
                    i32.ne
                    br_if 1 (;@7;)
                    local.get 11
                    i32.const 8
                    i32.add
                    local.set 0
                    local.get 17
                    i32.const 8
                    i32.add
                    local.set 3
                  end
                  block ;; label = @8
                    block ;; label = @9
                      local.get 3
                      local.get 5
                      i32.ge_u
                      br_if 0 (;@9;)
                      loop ;; label = @10
                        block ;; label = @11
                          local.get 0
                          i32.const 0
                          i32.const 4
                          call $readcheck
                          i32.load align=1
                          local.tee 6
                          local.get 3
                          i32.const 0
                          i32.const 4
                          call $readcheck
                          i32.load align=1
                          local.tee 4
                          i32.eq
                          br_if 0 (;@11;)
                          local.get 3
                          local.get 4
                          local.get 6
                          i32.xor
                          i32.ctz
                          i32.const 3
                          i32.shr_u
                          i32.add
                          local.set 3
                          br 3 (;@8;)
                        end
                        local.get 0
                        i32.const 4
                        i32.add
                        local.set 0
                        local.get 3
                        i32.const 4
                        i32.add
                        local.tee 3
                        local.get 5
                        i32.lt_u
                        br_if 0 (;@10;)
                      end
                    end
                    block ;; label = @9
                      local.get 3
                      local.get 16
                      i32.ge_u
                      br_if 0 (;@9;)
                      local.get 0
                      i32.const 0
                      i32.const 2
                      call $readcheck
                      i32.load16_u align=1
                      local.get 3
                      i32.const 0
                      i32.const 2
                      call $readcheck
                      i32.load16_u align=1
                      i32.ne
                      br_if 0 (;@9;)
                      local.get 0
                      i32.const 2
                      i32.add
                      local.set 0
                      local.get 3
                      i32.const 2
                      i32.add
                      local.set 3
                    end
                    local.get 3
                    local.get 15
                    i32.ge_u
                    br_if 0 (;@8;)
                    local.get 3
                    local.get 0
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    local.get 3
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    i32.eq
                    i32.add
                    local.set 3
                  end
                  local.get 17
                  local.get 3
                  local.get 13
                  i32.sub
                  local.tee 3
                  i32.add
                  i32.const 4
                  i32.add
                  local.set 17
                  local.get 3
                  i32.const 15
                  i32.lt_u
                  br_if 1 (;@6;)
                  local.get 20
                  local.get 20
                  i32.const 0
                  i32.const 1
                  call $readcheck
                  i32.load8_u
                  i32.const 15
                  i32.add
                  call $store_checked_0
                  local.get 21
                  i32.const -1
                  call $store_checked_6
                  block ;; label = @8
                    local.get 3
                    i32.const -15
                    i32.add
                    local.tee 0
                    i32.const 1020
                    i32.lt_u
                    br_if 0 (;@8;)
                    local.get 14
                    i32.const 6
                    i32.add
                    local.set 3
                    loop ;; label = @9
                      local.get 3
                      i32.const -1
                      call $store_checked_6
                      local.get 3
                      i32.const 4
                      i32.add
                      local.set 3
                      local.get 0
                      i32.const -1020
                      i32.add
                      local.tee 0
                      i32.const 1019
                      i32.gt_u
                      br_if 0 (;@9;)
                    end
                    local.get 3
                    i32.const -4
                    i32.add
                    local.set 21
                  end
                  local.get 21
                  local.get 0
                  i32.const 65535
                  i32.and
                  i32.const 255
                  i32.div_u
                  local.tee 3
                  i32.add
                  local.tee 6
                  local.get 0
                  local.get 3
                  i32.add
                  call $store_checked_0
                  local.get 6
                  i32.const 1
                  i32.add
                  local.set 21
                  br 2 (;@5;)
                end
                local.get 17
                local.get 0
                local.get 3
                i32.xor
                i32.ctz
                i32.const 3
                i32.shr_u
                local.tee 3
                i32.add
                i32.const 4
                i32.add
                local.set 17
              end
              local.get 20
              local.get 20
              i32.const 0
              i32.const 1
              call $readcheck
              i32.load8_u
              local.get 3
              i32.add
              call $store_checked_0
            end
            block ;; label = @5
              local.get 17
              local.get 18
              i32.lt_u
              br_if 0 (;@5;)
              local.get 21
              local.set 20
              local.get 17
              local.set 4
              br 3 (;@2;)
            end
            local.get 17
            i32.const -2
            i32.add
            local.tee 3
            i32.const 0
            i32.const 4
            call $readcheck
            i32.load align=1
            i32.const -1640531535
            i32.mul
            i32.const 20
            i32.shr_u
            local.set 0
            block ;; label = @5
              block ;; label = @6
                block ;; label = @7
                  local.get 10
                  br_if 0 (;@7;)
                  local.get 7
                  local.get 0
                  i32.const 2
                  i32.shl
                  i32.add
                  local.get 3
                  call $store_checked_7
                  local.get 7
                  local.get 17
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load align=1
                  local.tee 0
                  i32.const -1640531535
                  i32.mul
                  i32.const 18
                  i32.shr_u
                  i32.const 16380
                  i32.and
                  i32.add
                  local.tee 3
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load
                  local.set 11
                  local.get 3
                  local.get 17
                  call $store_checked_7
                  local.get 11
                  i32.const 65535
                  i32.add
                  local.get 17
                  i32.lt_u
                  br_if 1 (;@6;)
                  local.get 11
                  i32.const 0
                  i32.const 4
                  call $readcheck
                  i32.load align=1
                  local.get 0
                  i32.ne
                  br_if 1 (;@6;)
                  br 2 (;@5;)
                end
                local.get 7
                local.get 0
                i32.const 2
                i32.shl
                i32.add
                local.get 3
                local.get 19
                i32.sub
                call $store_checked_7
                local.get 7
                local.get 17
                i32.const 0
                i32.const 4
                call $readcheck
                i32.load align=1
                i32.const -1640531535
                i32.mul
                i32.const 18
                i32.shr_u
                i32.const 16380
                i32.and
                i32.add
                local.tee 0
                i32.const 0
                i32.const 4
                call $readcheck
                i32.load
                local.set 3
                local.get 0
                local.get 17
                local.get 19
                i32.sub
                local.tee 6
                call $store_checked_7
                local.get 3
                i32.const 65535
                i32.add
                local.get 6
                i32.lt_u
                br_if 0 (;@6;)
                local.get 19
                local.get 3
                i32.add
                local.tee 11
                i32.const 0
                i32.const 4
                call $readcheck
                i32.load align=1
                local.get 17
                i32.const 0
                i32.const 4
                call $readcheck
                i32.load align=1
                i32.eq
                br_if 1 (;@5;)
              end
              local.get 21
              local.set 20
              local.get 17
              local.set 4
              br 2 (;@3;)
            end
            local.get 21
            i32.const 0
            call $store_checked_0
            local.get 21
            i32.const 1
            i32.add
            local.set 14
            local.get 21
            local.set 20
            br 0 (;@4;)
          end
        end
      end
      local.get 20
      i32.const 1
      i32.add
      local.set 3
      block ;; label = @2
        block ;; label = @3
          local.get 9
          local.get 4
          i32.sub
          local.tee 5
          i32.const 15
          i32.lt_u
          br_if 0 (;@3;)
          local.get 20
          i32.const 240
          call $store_checked_0
          block ;; label = @4
            local.get 5
            i32.const -15
            i32.add
            local.tee 0
            i32.const 255
            i32.lt_u
            br_if 0 (;@4;)
            loop ;; label = @5
              local.get 3
              i32.const 255
              call $store_checked_0
              local.get 3
              i32.const 1
              i32.add
              local.set 3
              local.get 0
              i32.const -255
              i32.add
              local.tee 0
              i32.const 254
              i32.gt_u
              br_if 0 (;@5;)
            end
            local.get 3
            i32.const -1
            i32.add
            local.set 20
          end
          local.get 3
          local.get 0
          call $store_checked_0
          local.get 20
          i32.const 2
          i32.add
          local.set 3
          br 1 (;@2;)
        end
        local.get 20
        local.get 5
        i32.const 4
        i32.shl
        call $store_checked_0
      end
      local.get 3
      local.get 4
      local.get 5
      call 3
      drop
      local.get 3
      local.get 5
      i32.add
      local.get 2
      i32.sub
      return
    end
    local.get 11
    i32.const 1
    i32.add
    local.set 3
    block ;; label = @1
      block ;; label = @2
        local.get 10
        local.get 0
        i32.sub
        local.tee 7
        i32.const 15
        i32.lt_u
        br_if 0 (;@2;)
        local.get 11
        i32.const 240
        call $store_checked_0
        block ;; label = @3
          local.get 7
          i32.const -15
          i32.add
          local.tee 5
          i32.const 255
          i32.lt_u
          br_if 0 (;@3;)
          loop ;; label = @4
            local.get 3
            i32.const 255
            call $store_checked_0
            local.get 3
            i32.const 1
            i32.add
            local.set 3
            local.get 5
            i32.const -255
            i32.add
            local.tee 5
            i32.const 254
            i32.gt_u
            br_if 0 (;@4;)
          end
          local.get 3
          i32.const -1
          i32.add
          local.set 11
        end
        local.get 3
        local.get 5
        call $store_checked_0
        local.get 11
        i32.const 2
        i32.add
        local.set 3
        br 1 (;@1;)
      end
      local.get 11
      local.get 7
      i32.const 4
      i32.shl
      call $store_checked_0
    end
    local.get 3
    local.get 0
    local.get 7
    call 3
    drop
    local.get 3
    local.get 7
    i32.add
    local.get 2
    i32.sub
  )
  (func (;1;) (type 1) (param i32 i32 i32 i32) (result i32)
    (local i32)
    global.get 0
    i32.const 16416
    i32.sub
    local.tee 4
    global.set 0
    local.get 4
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    i32.const 1
    call 0
    local.set 3
    local.get 4
    i32.const 16416
    i32.add
    global.set 0
    local.get 3
  )
  (func (;2;) (type 1) (param i32 i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    i32.const -1
    local.set 4
    block ;; label = @1
      local.get 0
      i32.eqz
      br_if 0 (;@1;)
      local.get 3
      i32.const 0
      i32.lt_s
      br_if 0 (;@1;)
      block ;; label = @2
        local.get 3
        br_if 0 (;@2;)
        local.get 2
        i32.const 1
        i32.ne
        br_if 1 (;@1;)
        i32.const -1
        i32.const 0
        local.get 0
        i32.const 0
        i32.const 1
        call $readcheck
        i32.load8_u
        select
        return
      end
      local.get 2
      i32.eqz
      br_if 0 (;@1;)
      local.get 1
      local.get 3
      i32.add
      local.tee 5
      i32.const -32
      i32.add
      local.set 6
      local.get 0
      local.get 2
      i32.add
      local.tee 7
      i32.const -16
      i32.add
      local.set 8
      local.get 5
      i32.const -5
      i32.add
      local.set 9
      local.get 5
      i32.const -7
      i32.add
      local.set 10
      local.get 7
      i32.const -4
      i32.add
      local.set 11
      local.get 7
      i32.const -8
      i32.add
      local.set 12
      local.get 5
      i32.const -12
      i32.add
      local.set 13
      local.get 7
      i32.const -15
      i32.add
      local.set 14
      local.get 0
      local.set 4
      local.get 1
      local.set 3
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            loop ;; label = @5
              local.get 4
              i32.const 1
              i32.add
              local.set 15
              block ;; label = @6
                block ;; label = @7
                  block ;; label = @8
                    block ;; label = @9
                      local.get 4
                      i32.const 0
                      i32.const 1
                      call $readcheck
                      i32.load8_u
                      local.tee 16
                      i32.const 4
                      i32.shr_u
                      local.tee 2
                      i32.const 15
                      i32.eq
                      br_if 0 (;@9;)
                      block ;; label = @10
                        local.get 15
                        local.get 8
                        i32.lt_u
                        br_if 0 (;@10;)
                        local.get 15
                        local.set 4
                        br 2 (;@8;)
                      end
                      block ;; label = @10
                        local.get 3
                        local.get 6
                        i32.le_u
                        br_if 0 (;@10;)
                        local.get 15
                        local.set 4
                        br 2 (;@8;)
                      end
                      local.get 3
                      local.get 15
                      i32.const 16
                      call 3
                      drop
                      local.get 3
                      local.get 2
                      i32.add
                      local.tee 17
                      local.get 15
                      local.get 2
                      i32.add
                      local.tee 3
                      i32.const 0
                      i32.const 2
                      call $readcheck
                      i32.load16_u align=1
                      local.tee 18
                      i32.sub
                      local.set 2
                      local.get 3
                      i32.const 2
                      i32.add
                      local.set 4
                      local.get 16
                      i32.const 15
                      i32.and
                      local.tee 15
                      i32.const 15
                      i32.eq
                      br_if 2 (;@7;)
                      local.get 18
                      i32.const 8
                      i32.lt_u
                      br_if 2 (;@7;)
                      local.get 2
                      local.get 1
                      i32.lt_u
                      br_if 3 (;@6;)
                      local.get 17
                      local.get 2
                      i32.const 8
                      call 3
                      drop
                      local.get 17
                      i32.const 8
                      i32.add
                      local.get 2
                      i32.const 8
                      i32.add
                      i32.const 8
                      call 3
                      drop
                      local.get 17
                      i32.const 16
                      i32.add
                      local.get 2
                      i32.const 16
                      i32.add
                      i32.const 2
                      call 3
                      drop
                      local.get 17
                      local.get 15
                      i32.add
                      i32.const 4
                      i32.add
                      local.set 3
                      br 4 (;@5;)
                    end
                    block ;; label = @9
                      local.get 15
                      local.get 14
                      i32.lt_u
                      br_if 0 (;@9;)
                      local.get 15
                      local.set 4
                      br 7 (;@2;)
                    end
                    block ;; label = @9
                      local.get 4
                      i32.const 2
                      i32.add
                      local.tee 2
                      local.get 14
                      i32.le_u
                      br_if 0 (;@9;)
                      local.get 2
                      local.set 4
                      br 7 (;@2;)
                    end
                    block ;; label = @9
                      block ;; label = @10
                        local.get 15
                        i32.const 0
                        i32.const 1
                        call $readcheck
                        i32.load8_u
                        local.tee 17
                        i32.const 255
                        i32.eq
                        br_if 0 (;@10;)
                        local.get 2
                        local.set 4
                        br 1 (;@9;)
                      end
                      i32.const 255
                      local.set 17
                      loop ;; label = @10
                        local.get 2
                        i32.const 1
                        i32.add
                        local.tee 4
                        local.get 14
                        i32.gt_u
                        br_if 7 (;@3;)
                        local.get 17
                        local.get 2
                        i32.const 0
                        i32.const 1
                        call $readcheck
                        i32.load8_u
                        local.tee 15
                        i32.add
                        local.tee 17
                        i32.const 0
                        i32.lt_s
                        br_if 7 (;@3;)
                        local.get 4
                        local.set 2
                        local.get 15
                        i32.const 255
                        i32.eq
                        br_if 0 (;@10;)
                      end
                    end
                    local.get 17
                    i32.const 15
                    i32.add
                    local.tee 2
                    local.get 3
                    i32.const -1
                    i32.xor
                    i32.gt_u
                    br_if 6 (;@2;)
                    local.get 2
                    local.get 4
                    i32.const -1
                    i32.xor
                    i32.gt_u
                    br_if 6 (;@2;)
                  end
                  block ;; label = @8
                    block ;; label = @9
                      local.get 3
                      local.get 2
                      i32.add
                      local.tee 17
                      local.get 13
                      i32.gt_u
                      br_if 0 (;@9;)
                      local.get 4
                      local.get 2
                      i32.add
                      local.tee 18
                      local.get 12
                      i32.le_u
                      br_if 1 (;@8;)
                    end
                    local.get 4
                    local.get 2
                    i32.add
                    local.get 7
                    i32.ne
                    br_if 6 (;@2;)
                    local.get 17
                    local.get 5
                    i32.gt_u
                    br_if 6 (;@2;)
                    local.get 3
                    local.get 4
                    local.get 2
                    call 4
                    drop
                    local.get 17
                    local.get 1
                    i32.sub
                    return
                  end
                  loop ;; label = @8
                    local.get 3
                    local.get 4
                    i32.const 8
                    call 3
                    drop
                    local.get 4
                    i32.const 8
                    i32.add
                    local.set 4
                    local.get 3
                    i32.const 8
                    i32.add
                    local.tee 3
                    local.get 17
                    i32.lt_u
                    br_if 0 (;@8;)
                  end
                  local.get 16
                  i32.const 15
                  i32.and
                  local.set 15
                  local.get 18
                  i32.const 2
                  i32.add
                  local.set 4
                  local.get 17
                  local.get 18
                  i32.const 0
                  i32.const 2
                  call $readcheck
                  i32.load16_u align=1
                  local.tee 18
                  i32.sub
                  local.set 2
                end
                local.get 15
                i32.const 15
                i32.ne
                br_if 0 (;@6;)
                block ;; label = @7
                  local.get 4
                  i32.const 1
                  i32.add
                  local.tee 3
                  local.get 11
                  i32.le_u
                  br_if 0 (;@7;)
                  local.get 3
                  local.set 4
                  br 5 (;@2;)
                end
                block ;; label = @7
                  block ;; label = @8
                    local.get 4
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    local.tee 15
                    i32.const 255
                    i32.eq
                    br_if 0 (;@8;)
                    local.get 3
                    local.set 4
                    br 1 (;@7;)
                  end
                  i32.const 255
                  local.set 15
                  loop ;; label = @8
                    local.get 3
                    i32.const 1
                    i32.add
                    local.tee 4
                    local.get 11
                    i32.gt_u
                    br_if 4 (;@4;)
                    local.get 15
                    local.get 3
                    i32.const 0
                    i32.const 1
                    call $readcheck
                    i32.load8_u
                    local.tee 16
                    i32.add
                    local.tee 15
                    i32.const 0
                    i32.lt_s
                    br_if 4 (;@4;)
                    local.get 4
                    local.set 3
                    local.get 16
                    i32.const 255
                    i32.eq
                    br_if 0 (;@8;)
                  end
                end
                local.get 15
                i32.const 15
                i32.add
                local.tee 15
                local.get 17
                i32.const -1
                i32.xor
                i32.gt_u
                br_if 4 (;@2;)
              end
              local.get 2
              local.get 1
              i32.lt_u
              br_if 3 (;@2;)
              local.get 17
              local.get 15
              i32.add
              i32.const 4
              i32.add
              local.set 3
              block ;; label = @6
                block ;; label = @7
                  local.get 18
                  i32.const 7
                  i32.gt_u
                  br_if 0 (;@7;)
                  local.get 17
                  i32.const 0
                  call $store_checked_6
                  local.get 17
                  local.get 2
                  i32.const 0
                  i32.const 1
                  call $readcheck
                  i32.load8_u
                  call $store_checked_0
                  local.get 17
                  local.get 2
                  i32.const 1
                  i32.const 1
                  call $readcheck
                  i32.load8_u offset=1
                  call $store_checked_8
                  local.get 17
                  local.get 2
                  i32.const 2
                  i32.const 1
                  call $readcheck
                  i32.load8_u offset=2
                  call $store_checked_9
                  local.get 17
                  local.get 2
                  i32.const 3
                  i32.const 1
                  call $readcheck
                  i32.load8_u offset=3
                  call $store_checked_10
                  local.get 17
                  i32.const 4
                  i32.add
                  local.get 2
                  local.get 18
                  i32.const 2
                  i32.shl
                  local.tee 18
                  i32.const 65536
                  i32.const 4
                  call $readcheck
                  i32.load offset=65536
                  i32.add
                  local.tee 2
                  i32.const 4
                  call 3
                  drop
                  local.get 2
                  local.get 18
                  i32.const 65568
                  i32.const 4
                  call $readcheck
                  i32.load offset=65568
                  i32.sub
                  local.set 2
                  br 1 (;@6;)
                end
                local.get 17
                local.get 2
                i32.const 8
                call 3
                drop
                local.get 2
                i32.const 8
                i32.add
                local.set 2
              end
              local.get 17
              i32.const 8
              i32.add
              local.set 18
              block ;; label = @6
                local.get 3
                local.get 13
                i32.le_u
                br_if 0 (;@6;)
                local.get 3
                local.get 9
                i32.gt_u
                br_if 4 (;@2;)
                block ;; label = @7
                  local.get 18
                  local.get 10
                  i32.ge_u
                  br_if 0 (;@7;)
                  local.get 2
                  local.set 17
                  local.get 18
                  local.set 15
                  loop ;; label = @8
                    local.get 15
                    local.get 17
                    i32.const 8
                    call 3
                    drop
                    local.get 17
                    i32.const 8
                    i32.add
                    local.set 17
                    local.get 15
                    i32.const 8
                    i32.add
                    local.tee 15
                    local.get 10
                    i32.lt_u
                    br_if 0 (;@8;)
                  end
                  local.get 2
                  local.get 10
                  local.get 18
                  i32.sub
                  i32.add
                  local.set 2
                  local.get 10
                  local.set 18
                end
                local.get 18
                local.get 3
                i32.ge_u
                br_if 1 (;@5;)
                loop ;; label = @7
                  local.get 18
                  local.get 2
                  i32.const 0
                  i32.const 1
                  call $readcheck
                  i32.load8_u
                  call $store_checked_0
                  local.get 2
                  i32.const 1
                  i32.add
                  local.set 2
                  local.get 18
                  i32.const 1
                  i32.add
                  local.tee 18
                  local.get 3
                  i32.lt_u
                  br_if 0 (;@7;)
                  br 2 (;@5;)
                end
              end
              local.get 18
              local.get 2
              i32.const 8
              call 3
              drop
              local.get 15
              i32.const 13
              i32.lt_u
              br_if 0 (;@5;)
              local.get 2
              i32.const 8
              i32.add
              local.set 2
              local.get 17
              i32.const 16
              i32.add
              local.set 17
              loop ;; label = @6
                local.get 17
                local.get 2
                i32.const 8
                call 3
                drop
                local.get 2
                i32.const 8
                i32.add
                local.set 2
                local.get 17
                i32.const 8
                i32.add
                local.tee 17
                local.get 3
                i32.lt_u
                br_if 0 (;@6;)
                br 1 (;@5;)
              end
            end
          end
          local.get 3
          i32.const 1
          i32.add
          local.set 4
          br 1 (;@2;)
        end
        local.get 2
        i32.const 1
        i32.add
        local.set 4
      end
      local.get 4
      i32.const -1
      i32.xor
      local.get 0
      i32.add
      local.set 4
    end
    local.get 4
  )
  (func (;3;) (type 2) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32)
    block ;; label = @1
      local.get 2
      i32.eqz
      br_if 0 (;@1;)
      local.get 2
      i32.const 3
      i32.and
      local.set 3
      i32.const 0
      local.set 4
      block ;; label = @2
        local.get 2
        i32.const 4
        i32.lt_u
        br_if 0 (;@2;)
        local.get 2
        i32.const -4
        i32.and
        local.set 5
        i32.const 0
        local.set 4
        loop ;; label = @3
          local.get 0
          local.get 4
          i32.add
          local.tee 2
          local.get 1
          local.get 4
          i32.add
          local.tee 6
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 2
          i32.const 1
          i32.add
          local.get 6
          i32.const 1
          i32.add
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 2
          i32.const 2
          i32.add
          local.get 6
          i32.const 2
          i32.add
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 2
          i32.const 3
          i32.add
          local.get 6
          i32.const 3
          i32.add
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 5
          local.get 4
          i32.const 4
          i32.add
          local.tee 4
          i32.ne
          br_if 0 (;@3;)
        end
        local.get 3
        i32.eqz
        br_if 1 (;@1;)
      end
      local.get 1
      local.get 4
      i32.add
      local.set 2
      local.get 0
      local.get 4
      i32.add
      local.set 4
      loop ;; label = @2
        local.get 4
        local.get 2
        i32.const 0
        i32.const 1
        call $readcheck
        i32.load8_u
        call $store_checked_0
        local.get 2
        i32.const 1
        i32.add
        local.set 2
        local.get 4
        i32.const 1
        i32.add
        local.set 4
        local.get 3
        i32.const -1
        i32.add
        local.tee 3
        br_if 0 (;@2;)
      end
    end
    local.get 0
  )
  (func (;4;) (type 2) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32)
    block ;; label = @1
      block ;; label = @2
        local.get 0
        local.get 1
        i32.lt_u
        br_if 0 (;@2;)
        local.get 2
        i32.eqz
        br_if 1 (;@1;)
        local.get 2
        local.set 3
        block ;; label = @3
          local.get 2
          i32.const 3
          i32.and
          local.tee 4
          i32.eqz
          br_if 0 (;@3;)
          local.get 1
          i32.const -1
          i32.add
          local.set 5
          local.get 0
          i32.const -1
          i32.add
          local.set 6
          local.get 2
          local.set 3
          loop ;; label = @4
            local.get 6
            local.get 3
            i32.add
            local.get 5
            local.get 3
            i32.add
            i32.const 0
            i32.const 1
            call $readcheck
            i32.load8_u
            call $store_checked_0
            local.get 3
            i32.const -1
            i32.add
            local.set 3
            local.get 4
            i32.const -1
            i32.add
            local.tee 4
            br_if 0 (;@4;)
          end
        end
        local.get 2
        i32.const 4
        i32.lt_u
        br_if 1 (;@1;)
        local.get 1
        i32.const -4
        i32.add
        local.set 6
        local.get 0
        i32.const -4
        i32.add
        local.set 1
        loop ;; label = @3
          local.get 1
          local.get 3
          i32.add
          local.tee 4
          i32.const 3
          i32.add
          local.get 6
          local.get 3
          i32.add
          local.tee 5
          i32.const 3
          i32.add
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 4
          i32.const 2
          i32.add
          local.get 5
          i32.const 2
          i32.add
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 4
          i32.const 1
          i32.add
          local.get 5
          i32.const 1
          i32.add
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 4
          local.get 5
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 3
          i32.const -4
          i32.add
          local.tee 3
          br_if 0 (;@3;)
          br 2 (;@1;)
        end
      end
      local.get 2
      i32.eqz
      br_if 0 (;@1;)
      local.get 2
      i32.const 3
      i32.and
      local.set 6
      i32.const 0
      local.set 4
      block ;; label = @2
        local.get 2
        i32.const 4
        i32.lt_u
        br_if 0 (;@2;)
        local.get 2
        i32.const -4
        i32.and
        local.set 2
        i32.const 0
        local.set 4
        loop ;; label = @3
          local.get 0
          local.get 4
          i32.add
          local.tee 3
          local.get 1
          local.get 4
          i32.add
          local.tee 5
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 3
          i32.const 1
          i32.add
          local.get 5
          i32.const 1
          i32.add
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 3
          i32.const 2
          i32.add
          local.get 5
          i32.const 2
          i32.add
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 3
          i32.const 3
          i32.add
          local.get 5
          i32.const 3
          i32.add
          i32.const 0
          i32.const 1
          call $readcheck
          i32.load8_u
          call $store_checked_0
          local.get 2
          local.get 4
          i32.const 4
          i32.add
          local.tee 4
          i32.ne
          br_if 0 (;@3;)
        end
        local.get 6
        i32.eqz
        br_if 1 (;@1;)
      end
      local.get 1
      local.get 4
      i32.add
      local.set 3
      local.get 0
      local.get 4
      i32.add
      local.set 4
      loop ;; label = @2
        local.get 4
        local.get 3
        i32.const 0
        i32.const 1
        call $readcheck
        i32.load8_u
        call $store_checked_0
        local.get 3
        i32.const 1
        i32.add
        local.set 3
        local.get 4
        i32.const 1
        i32.add
        local.set 4
        local.get 6
        i32.const -1
        i32.add
        local.tee 6
        br_if 0 (;@2;)
      end
    end
    local.get 0
  )
  (func (;5;) (type 2) (param i32 i32 i32) (result i32)
    (local i32 i32 i32)
    block ;; label = @1
      local.get 2
      i32.eqz
      br_if 0 (;@1;)
      local.get 2
      i32.const 7
      i32.and
      local.set 3
      i32.const 0
      local.set 4
      block ;; label = @2
        local.get 2
        i32.const 8
        i32.lt_u
        br_if 0 (;@2;)
        local.get 2
        i32.const -8
        i32.and
        local.set 5
        i32.const 0
        local.set 4
        loop ;; label = @3
          local.get 0
          local.get 4
          i32.add
          local.tee 2
          local.get 1
          call $store_checked_0
          local.get 2
          i32.const 7
          i32.add
          local.get 1
          call $store_checked_0
          local.get 2
          i32.const 6
          i32.add
          local.get 1
          call $store_checked_0
          local.get 2
          i32.const 5
          i32.add
          local.get 1
          call $store_checked_0
          local.get 2
          i32.const 4
          i32.add
          local.get 1
          call $store_checked_0
          local.get 2
          i32.const 3
          i32.add
          local.get 1
          call $store_checked_0
          local.get 2
          i32.const 2
          i32.add
          local.get 1
          call $store_checked_0
          local.get 2
          i32.const 1
          i32.add
          local.get 1
          call $store_checked_0
          local.get 5
          local.get 4
          i32.const 8
          i32.add
          local.tee 4
          i32.ne
          br_if 0 (;@3;)
        end
        local.get 3
        i32.eqz
        br_if 1 (;@1;)
      end
      local.get 0
      local.get 4
      i32.add
      local.set 2
      loop ;; label = @2
        local.get 2
        local.get 1
        call $store_checked_0
        local.get 2
        i32.const 1
        i32.add
        local.set 2
        local.get 3
        i32.const -1
        i32.add
        local.tee 3
        br_if 0 (;@2;)
      end
    end
    local.get 0
  )
  (data (;0;) (i32.const 65536) "\00\00\00\00\01\00\00\00\02\00\00\00\01\00\00\00\00\00\00\00\04\00\00\00\04\00\00\00\04\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\ff\ff\ff\ff\fc\ff\ff\ff\01\00\00\00\02\00\00\00\03\00\00\00")
(global $sb (mut i32) (i32.const 0))
(global $se (mut i32) (i32.const 0))
(global $db (mut i32) (i32.const 0))
(global $de (mut i32) (i32.const 0))
(func (export "verify_config") (param i32 i32 i32 i32)
              local.get 0 global.set $sb local.get 1 global.set $se
              local.get 2 global.set $db local.get 3 global.set $de)
(func $readcheck (param $a i32) (param $off i32) (param $n i32) (result i32)
        (local $p i64) (local $q i64)
        local.get $a i64.extend_i32_u local.get $off i64.extend_i32_u i64.add local.tee $p
        local.get $n i64.extend_i32_u i64.add local.tee $q
        i64.const 131072 i64.le_u
        local.get $p global.get $db i64.extend_i32_u i64.ge_u local.get $q global.get $de i64.extend_i32_u i64.le_u i32.and local.get $p global.get $sb i64.extend_i32_u i64.ge_u local.get $q global.get $se i64.extend_i32_u i64.le_u i32.and i32.or i32.or i32.eqz if unreachable end local.get $a)
(func $writecheck (param $a i32) (param $off i32) (param $n i32) (result i32)
        (local $p i64) (local $q i64)
        local.get $a i64.extend_i32_u local.get $off i64.extend_i32_u i64.add local.tee $p
        local.get $n i64.extend_i32_u i64.add local.tee $q
        i64.const 131072 i64.le_u
        local.get $p global.get $db i64.extend_i32_u i64.ge_u local.get $q global.get $de i64.extend_i32_u i64.le_u i32.and i32.or i32.eqz if unreachable end local.get $a)
(func $store_checked_0 (param i32 i32)
              local.get 0 i32.const 0 i32.const 1 call $writecheck
              local.get 1 i32.store8)
(func $store_checked_1 (param i32 i32)
              local.get 0 i32.const 16396 i32.const 4 call $writecheck
              local.get 1 i32.store offset=16396)
(func $store_checked_2 (param i32 i32)
              local.get 0 i32.const 16400 i32.const 4 call $writecheck
              local.get 1 i32.store offset=16400)
(func $store_checked_3 (param i32 i32)
              local.get 0 i32.const 16392 i32.const 4 call $writecheck
              local.get 1 i32.store offset=16392)
(func $store_checked_4 (param i32 i32)
              local.get 0 i32.const 0 i32.const 2 call $writecheck
              local.get 1 i32.store16)
(func $store_checked_5 (param i32 i32)
              local.get 0 i32.const 0 i32.const 2 call $writecheck
              local.get 1 i32.store16 align=1)
(func $store_checked_6 (param i32 i32)
              local.get 0 i32.const 0 i32.const 4 call $writecheck
              local.get 1 i32.store align=1)
(func $store_checked_7 (param i32 i32)
              local.get 0 i32.const 0 i32.const 4 call $writecheck
              local.get 1 i32.store)
(func $store_checked_8 (param i32 i32)
              local.get 0 i32.const 1 i32.const 1 call $writecheck
              local.get 1 i32.store8 offset=1)
(func $store_checked_9 (param i32 i32)
              local.get 0 i32.const 2 i32.const 1 call $writecheck
              local.get 1 i32.store8 offset=2)
(func $store_checked_10 (param i32 i32)
              local.get 0 i32.const 3 i32.const 1 call $writecheck
              local.get 1 i32.store8 offset=3)
)
