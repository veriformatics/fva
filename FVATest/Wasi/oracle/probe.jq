def sig($c):
  {args_sizes_get:["i32","i32"],args_get:["i32","i32"],
   environ_sizes_get:["i32","i32"],environ_get:["i32","i32"],
   clock_time_get:["i32","i64","i32"],fd_close:["i32"],
   fd_fdstat_get:["i32","i32"],fd_fdstat_set_flags:["i32","i32"],
   fd_prestat_get:["i32","i32"],fd_prestat_dir_name:["i32","i32","i32"],
   fd_read:["i32","i32","i32","i32"],fd_write:["i32","i32","i32","i32"],
   fd_seek:["i32","i64","i32","i32"],path_open:["i32","i32","i32","i32","i32","i64","i64","i32","i32"],
   path_create_directory:["i32","i32","i32"],path_remove_directory:["i32","i32","i32"],
   path_unlink_file:["i32","i32","i32"],path_filestat_get:["i32","i32","i32","i32","i32"],
   proc_exit:["i32"],random_get:["i32","i32"]}[$c] // error("unsupported call " + $c);
def utf8:
  [explode[] | if .<128 then . elif .<2048 then (192+(./64|floor)),(128+(.%64))
   elif .<65536 then (224+(./4096|floor)),(128+((./64|floor)%64)),(128+(.%64))
   else (240+(./262144|floor)),(128+((./4096|floor)%64)),(128+((./64|floor)%64)),(128+(.%64)) end];
def bytes:
  if has("text") then .text | utf8
  elif has("hex") then [.hex | ascii_downcase | scan("..") | explode
    | map(if .<=57 then .-48 else .-87 end) | .[0]*16+.[1]]
  else error("expected byte object") end;
def runs:
  reduce to_entries[] as $b ([];
    if length>0 and .[-1].byte==$b.value then .[-1].len+=1
    else .+[{offset:$b.key,byte:$b.value,len:1}] end);
def cn($t;$n): "("+$t+".const "+($n|tostring)+")";
def callExpr($s):
  sig($s.call) as $ts | "(call $"+$s.call+" "+
    ([$s.args|to_entries[]|cn($ts[.key];.value)]|join(" "))+")";
def initMem:
  .addr as $a |
  if has("u32") then .u32|to_entries[]|"(i32.store "+cn("i32";($a+4*.key))+" "+cn("i32";.value)+")"
  elif has("u64") then .u64|to_entries[]|"(i64.store "+cn("i32";($a+8*.key))+" "+cn("i64";.value)+")"
  else bytes|runs|.[]|
    if .len>=8 then "(memory.fill "+cn("i32";($a+.offset))+" "+cn("i32";.byte)+" "+cn("i32";.len)+")"
    else . as $r | range(0;.len)|"(i32.store8 "+cn("i32";($a+$r.offset+.))+" "+cn("i32";$r.byte)+")" end end;
def memObs($step;$basis):
  .addr as $a |
  if has("u32") then .u32|to_entries[]|
    {step:$step,basis:$basis,label:("mem["+($a+4*.key|tostring)+"].u32"),
     expected:(.value|tostring),expr:("(i64.extend_i32_u (i32.load "+cn("i32";($a+4*.key))+"))")}
  elif has("u64") then .u64|to_entries[]|
    {step:$step,basis:$basis,label:("mem["+($a+8*.key|tostring)+"].u64"),
     expected:(.value|tostring),expr:("(i64.load "+cn("i32";($a+8*.key))+")")}
  else
    (bytes|runs|map("(call $all "+cn("i32";($a+.offset))+" "+cn("i32";.len)+" "+cn("i32";.byte)+")")) as $rs |
    {step:$step,basis:$basis,label:("mem["+($a|tostring)+"].bytes"),expected:"1",
     expr:(reduce $rs[] as $x ("(i64.const 1)"; "(i64.and "+.+" "+$x+")"))}
  end;
def observations:
  [.steps|to_entries[] | .key as $k | .value as $s |
   if $s.expect.outcome=="exit" then empty
   else {step:$k,basis:$s.expect.basis,label:"errno",expected:($s.expect.errno//0|tostring),expr:null},
     ($s.expect.mem[]? | memObs($k;$s.expect.basis)) end];
def probe:
  . as $v | observations|to_entries as $obs |
  [";; Generated from vectors/"+$v.id+".json by oracle/make; WASI values remain source-derived.",
   "(module",
   ([$v.steps[].call]|unique[] | . as $c | sig($c) as $ts |
    "  (import \"wasi_snapshot_preview1\" \""+$c+"\" (func $"+$c+
    " (param "+($ts|join(" "))+")"+(if $c=="proc_exit" then "" else " (result i32)" end)+"))"),
   "  (memory (export \"memory\") "+($v.pages|tostring)+")",
   "  (func $all (param $a i32) (param $n i32) (param $v i32) (result i64)",
   "    (local $i i32)",
   "    (block $bad (loop $next",
   "      (if (i32.ge_u (local.get $i) (local.get $n)) (then (return (i64.const 1))))",
   "      (br_if $bad (i32.ne (i32.load8_u (i32.add (local.get $a) (local.get $i))) (local.get $v)))",
   "      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $next)))",
   "    (i64.const 0))",
   ("  (func (export \"_start\")"+(if ($obs|length)>0 then " (result "+([$obs[]|"i64"]|join(" "))+")" else "" end)),
   ($obs[]|"    (local $o"+(.key|tostring)+" i64)"),
   ($v.steps|to_entries[] | .key as $k | .value as $s |
    "    ;; step "+($k|tostring)+": "+$s.call+"; "+$s.expect.basis,
    ($s.mem[]? | initMem | "    "+.),
    (if $s.call=="proc_exit" then "    "+callExpr($s),"    (unreachable)"
     else ($obs[]|select(.value.step==$k and .value.label=="errno")|
      "    (local.set $o"+(.key|tostring)+" (i64.extend_i32_u "+callExpr($s)+"))"),
      ($obs[]|select(.value.step==$k and .value.label!="errno")|
       "    (local.set $o"+(.key|tostring)+" "+.value.expr+")") end)),
   ($obs[]|"    (local.get $o"+(.key|tostring)+")"),
   "  )",
   ")"] | join("\n");
