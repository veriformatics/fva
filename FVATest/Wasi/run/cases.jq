# Contract-derived fixtures + fixed-seed generated domains. Expected oracle bytes are
# replayed by `check wasmtime`; oracle.tsv records their observed capture hashes.
def text($s): {text:$s};
def hex($s): {hex:$s};
def d($p): {path:$p,kind:"d"};
def f($p;$b): {path:$p,kind:"f",bytes:$b};
def base: [d("roots"),d("roots/one"),d("roots/one/nested"),d("roots/one/nested/empty"),
  f("roots/one/keep.bin";hex("00ff10200a")),f("untouched sibling";text("outside preopens\n"))];
def before: base + [f("roots/one/delete.bin";text("delete me")),f("roots/one/seed.bin";text("truncate me\n"))];
def after($t): $t | map(select(.path != "roots/one/delete.bin" and .path != "roots/one/seed.bin"))
  + [f("roots/one/seed.bin";text("")),f("roots/one/effect.bin";hex("00ff4656410a"))];
def mapping: ["--dir","roots/one::/sandbox"];
def c($id;$rows;$p;$basis;$tree):
  {id:$id,rows:$rows,program:$p,basis:$basis,opts:[],args:[],stdin:text(""),tree:$tree,
   expect:{stdout:text(""),stderr:text(""),rc:0,tree:$tree}};
def envOf($opts): [range(0;$opts|length) as $i | select($opts[$i]=="--env") | $opts[$i+1]];
def process($id;$rows;$args;$opts;$in;$tree):
  c($id;$rows;"process";"wasmtime";$tree) | .args=$args | .opts=$opts | .stdin=text($in)
  | .expect.stdout=text("ARGS\u0000process.wasm\u0000"+([$args[]+"\u0000"]|join(""))
    +"ENV\u0000"+([envOf($opts)[]+"\u0000"]|join(""))+"STDIN\u0000"+$in);
def effects($id;$p;$basis;$rc):
  c($id;["X1","O1","D3"];$p;$basis;before) | .opts=mapping
  | .expect={stdout:text("A|C|"),stderr:text("B|D|"),rc:$rc,tree:after(before)};
def reject($id;$rows;$p;$name;$tree;$opts):
  c($id;$rows;$p;"departure:"+$name;$tree) | .opts=$opts | .expect.rc=2 | .diagnostic=true;
def lcg($n): (($n*1664525+1013904223)%4294967296);
def sample($seed;$n):
  [""," ","two words","βeta","生物","--env","--","=","a=b=c","\t","\n","-x","é","🙂"] as $a
  | [range(0;$n) as $i | $a[(lcg($seed+$i*97)%($a|length))]];
def parserProps:
  range(0;24) as $i | (sample(271828+$i;5)) as $a
  | ["--env","DUP="+$a[0],"--dir","roots/one::./guest/../literal",
     "--env","DUP="+$a[1]+"=tail","--env","EMPTY=","--env","UNICODE="+$a[2]] as $o
  | process("prop-parser-\($i)";["P1","A1","A2"];$a;$o;("stdin:"+$a[3]+"\n");base)
  | if $i%2==0 then .opts=(["--dir","roots/one::./guest/../literal"]+$o[0:2]+$o[4:]) else . end;
def treeProps:
  range(0;24) as $i | sample(314159+$i;5) as $a
  | (before+[d("roots/one/empty-\($i)"),d("roots/one/nested/β \($i)"),
      f("roots/one/nested/β \($i)/--=\nfile";text($a[0]+"\u0000"+$a[1])),
      f("roots/one/empty-file-\($i)";text("")),f("roots/one/ends-with-newline-\($i)\n";text("tail\n")),
      f("roots/one/bytes-\($i)";hex("0001027f80feff00"))]) as $t
  | if $i%2==0 then
      c("prop-tree-\($i)";["P1","D2"];"noop";"wasmtime";$t) | .opts=mapping
    else
      effects("prop-tree-\($i)";"return";"wasmtime";0) | .rows=["P1","D2","D3"]
      | .tree=$t | .expect.tree=after($t)
    end;
[
  process("process-empty";["A1","A2"];[];[];"";[]),
  process("process-values";["A1","A2"];["","two words","βeta","--looks-like-option","--","--env","K=guest"];
    ["--env","DUP=first","--env","EMPTY=","--env","DUP=second","--env","EQUAL=a=b=c"];
    "stdin with spaces\nβ\n";[]),
  process("env-empty-keys";["A2"];[];["--env","=value","--env","=","--env","β=unicode","--env","--looks=like=an=option"];"";[]),
  (c("fuel-leading-zeroes";["P1"];"noop";"departure:step-limit";[]) | .opts=["--fuel","0005000"]),
  (process("process-basename";["A1"];["argument"];[];"";[]) | .wasmName="a name β.wasm"
    | .expect.stdout=text("ARGS\u0000a name β.wasm\u0000argument\u0000ENV\u0000STDIN\u0000")),
  (c("dir-host-only";["D1"];"preopens";"wasmtime";base)
    | .opts=["--dir","roots/one/../one"] | .expect.stdout=text("PRE\u0000roots/one/../one\u0000")),
  (c("dir-literal-guest";["D1"];"preopens";"wasmtime";base)
    | .opts=["--dir","roots/one::./guest/../literal"] | .expect.stdout=text("PRE\u0000./guest/../literal\u0000")),
  (c("dir-multiple-names";["D1"];"preopens";"wasmtime";base+[d("roots/two")])
    | .opts=["--dir","roots/two::β root","--dir","roots/one::."] | .expect.stdout=text("PRE\u0000β root\u0000.\u0000")),
  (c("dir-multiple-effects";["D1","D3"];"multi";"wasmtime";base+[d("roots/two")])
    | .opts=["--dir","roots/one::/one","--dir","roots/two::/two"]
    | .expect.tree += [f("roots/one/effect.bin";hex("00ff")),f("roots/two/effect.bin";text("FVA\n"))]),
  (c("dir-prefix-siblings";["D1"];"multi";"wasmtime";base+[d("roots/one-more")])
    | .opts=["--dir","roots/one::/one","--dir","roots/one-more::/two"]
    | .expect.tree += [f("roots/one/effect.bin";hex("00ff")),f("roots/one-more/effect.bin";text("FVA\n"))]),
  (c("files-all";["D2","D3"];"files";"wasmtime";
      base+[f("roots/one/truncate.bin";text("long old bytes\n")),f("roots/one/gone.bin";hex("00ff")),
        d("roots/one/oldkind"),f("roots/one/newkind";text("was a file")),f("roots/one/orphan.bin";hex("4f4c4400ff"))])
    | .opts=mapping | .expect.stdout=hex("4f4c4400ff")
    | .expect.tree=base+[f("roots/one/nested/new.bin";hex("00ff7879")),f("roots/one/truncate.bin";text("")),
      f("roots/one/oldkind";text("")),d("roots/one/newkind"),f("roots/one/orphan.bin";text("NEW")),
      d("roots/one/created"),f("roots/one/zero.bin";text(""))]),
  effects("return-effects";"return";"wasmtime";0),
  effects("exit0-effects";"exit0";"wasmtime";0),
  effects("exit7-effects";"exit7";"wasmtime";7),
  effects("exit125-effects";"exit125";"wasmtime";125),
  (effects("exit126-effects";"exit126";"departure:large-exit";1) | .diagnostic=true | .diagnosticContains=["126"]),
  (effects("exitmax-effects";"exitmax";"departure:large-exit";1) | .diagnostic=true | .diagnosticContains=["4294967295"]),
  (effects("trap-effects";"trap";"departure:diagnostics";134) | .diagnostic=true),
  (effects("trap-control-frames";"trap-frames";"departure:diagnostics";134) | .diagnostic=true),
  (effects("exception-effects";"exception";"departure:diagnostics";1) | .diagnostic=true),
  (effects("diagnostic-marker";"diagnostic-marker";"departure:diagnostics";134)
    | .rows=["O1","X1"] | .diagnostic=true
    | .expect.stderr=hex("427c447c6676612072756e3a2067756573740a5800ff6676612072756e3a206775657374207461696c")),
  (effects("fuel-effects";"fuel";"departure:step-limit";2) | .rows=["X3","D3"]
    | .opts += ["--fuel","5000"] | .diagnostic=true),
  (reject("fuel-zero";["X3"];"return";"step-limit";before;mapping+["--fuel","0"]) | .diagnostic=true),
  (effects("nan-effects";"nan";"departure:nonunique-numeric-choice";2) | .rows=["X3","D3"] | .diagnostic=true),
  (effects("out-of-profile-effects";"unsupported";"departure:out-of-profile-stop";2)
    | .rows=["X1","D3"] | .diagnostic=true),
  (effects("out-of-bounds-write";"unsupported-oob";"departure:out-of-profile-stop";2)
    | .rows=["X1","D3"] | .diagnostic=true),
  (c("visibility";["O1"];"visibility";"relational";[]) | .mode="visibility"),
  (effects("stream-order";"return";"wasmtime";0) | .rows=["O1"] | .merged=text("A|B|C|D|")),
  (c("random-default";["O2"];"random";"relational";[]) | .mode="random"),
  (c("random-padded";["O2"];"random";"departure:fixed-bytes-random";[]) | .opts=["--random","0011ff"]
    | .expect.stdout=hex(([range(0;2)|"0011ff"+([range(0;29)|"00"]|join(""))]|join("")))
    | .diagnostic=true),
  (c("random-uppercase";["O2"];"random";"departure:fixed-bytes-random";[]) | .opts=["--random","A0B1FF"]
    | .expect.stdout=hex(([range(0;2)|"a0b1ff"+([range(0;29)|"00"]|join(""))]|join("")))
    | .diagnostic=true),
  (c("random-cut";["O2"];"random";"departure:fixed-bytes-random";[])
    | .opts=["--random",([range(0;40)|"ab"]|join(""))]
    | .expect.stdout=hex([range(0;64)|"ab"]|join("")) | .diagnostic=true),
  (c("clocks-frozen";["X1"];"clock";"departure:frozen-clocks";[])
    | .expect.stdout=hex([range(0;16)|"00"]|join(""))),
  reject("dir-overlap-same";["D1"];"return";"filesystem-shape";before;
    ["--dir","roots/one::/a","--dir","roots/one/../one::/b"]),
  reject("dir-overlap-child";["D1"];"return";"filesystem-shape";before;
    ["--dir","roots/one::/a","--dir","roots/one/nested::/b"]),
  reject("reject-symlink";["D4"];"return";"filesystem-shape";before+[{path:"roots/one/link",kind:"l",target:"keep.bin"}];mapping),
  reject("reject-fifo";["D4"];"return";"filesystem-shape";before+[{path:"roots/one/pipe",kind:"p"}];mapping),
  reject("reject-hardlink";["D4"];"return";"filesystem-shape";before+[{path:"roots/one/alias",kind:"h",target:"roots/one/keep.bin"}];mapping),
  reject("reject-file-root";["D4"];"return";"filesystem-shape";before;["--dir","roots/one/keep.bin"]),
  reject("reject-missing-root";["D4"];"return";"filesystem-shape";before;["--dir","roots/absent"]),
  (reject("read-file-failure";["F1"];"return";"host-io-failure";before;mapping)
    | .modes=[{path:"roots/one/keep.bin",mode:"000"}] | .diagnostic=true | .diagnosticContains=["keep.bin"]),
  (reject("stdin-read-failure";["F1"];"return";"host-io-failure";before;mapping)
    | .mode="stdin-directory" | .diagnostic=true),
  (reject("sync-create-failure";["F1"];"sync";"host-io-failure";base;mapping)
    | .modes=[{path:"roots/one",mode:"500"}] | .expect.stdout=text("S\n") | .diagnostic=true | .diagnosticContains=["roots/one"]),
  (effects("stdout-write-failure";"return";"departure:host-io-failure";2)
    | .rows=["F1"] | .mode="stdout-full" | .expect.stdout=text("") | .expect.stderr=text("") | .diagnostic=true),
  (effects("stderr-write-failure";"return";"departure:host-io-failure";2)
    | .rows=["F1"] | .mode="stderr-full" | .expect.stdout=text("A|") | .expect.stderr=text("")),
  (["load-start","load-initialize","load-no-start","load-start-param","load-start-result","load-no-memory",
    "load-memory-import","load-invalid","load-undecodable","load-unresolved","load-other-preview1","load-wrong-import-type"][] as $p
    | reject($p;["X2"];$p;"load-rejection";before;mapping)),
  ([{id:"option-unknown",opts:["--not-an-option"]},
    {id:"option-dir-missing",opts:["--dir"]},{id:"option-env-missing",opts:["--env"]},
    {id:"option-random-missing",opts:["--random"]},{id:"option-fuel-missing",opts:["--fuel"]},
    {id:"option-env-no-equals",opts:["--env","NO_EQUALS"]},
    {id:"option-random-odd",opts:["--random","abc"]},{id:"option-random-nonhex",opts:["--random","0x01"]},
    {id:"option-fuel-negative",opts:["--fuel","-1"]},{id:"option-fuel-garbage",opts:["--fuel","12x"]},
    {id:"option-fuel-empty",opts:["--fuel",""]}][] as $o
    | reject($o.id;["F2","A2"];"return";"option-rejection";before;mapping+$o.opts) | .omitDelimiter=true),
  parserProps,
  treeProps
] | {version:1,oracle:{name:"wasmtime",version:"50.0.0",flags:[]},
  properties:{parser:{seed:271828,count:24},tree:{seed:314159,count:24}},cases:.}
