# Inputs = frozen U29a v2 contract + WITX fae981ba + wasmtime 50.0.0 p1.
def bits($xs): reduce $xs[] as $b (0; . + pow(2; $b));
def wr: bits([0,2,3,4,5,6,7,8,21,22,23,27]);
def preBase: bits([0,4,9,10,11,12,13,14,15,16,17,18,19,20,21,23,24,25,26]);
def preInh: bits([range(0;28)]);
def tree: {f:{file:{text:"abc"}},d:{dir:{}}};
def world: {args:["p"],env:[],stdin:{text:""},clocks:[123456789,87654321,0,0],dirs:[{guest:".",tree:tree}]};
def cell($a;$vs): {addr:$a,u32:$vs};
def wide($a;$vs): {addr:$a,u64:$vs};
def text($a;$s): {addr:$a,text:$s};
def hex($a;$s): {addr:$a,hex:$s};
def step($c;$a;$e;$m): {mem:[],call:$c,args:$a,expect:{outcome:"errno",errno:$e,mem:$m,basis:"wasmtime"}};
def contract: .expect.basis = "contract";
def outside: .expect = {outcome:"out-of-profile",basis:"wasmtime"};
def init($m): .mem = $m;
def open($path;$flags;$base;$inh;$fdflags;$e;$fd):
  step("path_open";[3,0,128,($path|utf8bytelength),$flags,$base,$inh,$fdflags,32];$e;
       if $e == 0 then [cell(32;[$fd])] else [cell(32;[0])] end)
  | init([text(128;$path)]);
def fileOpen: open("f";0;110;0;0;0;4);
def read($fd;$len;$value):
  step("fd_read";[$fd,0,1,32];0;[cell(32;[($value|utf8bytelength)]),text(256;$value)])
  | init([cell(0;[256,$len])]);
def write($fd;$s):
  step("fd_write";[$fd,0,1,32];0;[cell(32;[($s|utf8bytelength)])])
  | init([cell(0;[256,($s|utf8bytelength)]),text(256;$s)]);
def seek($fd;$delta;$whence;$e;$pos):
  step("fd_seek";[$fd,$delta,$whence,40];$e;[wide(40;[$pos])]);
def path($call;$s;$e): step($call;[3,128,($s|utf8bytelength)];$e;[]) | init([text(128;$s)]);
def stat($s;$flags;$e;$mem):
  step("path_filestat_get";[3,$flags,128,($s|utf8bytelength),256];$e;$mem)
  | init([text(128;$s)]);
def v($row;$id;$sources;$steps):
  {row:$row,id:$id,sources:($sources + ["probe " + $id]),world:world,pages:1,steps:$steps,
   final:{stdout:{text:""},stderr:{text:""},files:{".":tree}}};
def fdstat($type;$base;$inh): [cell(256;[$type]),cell(260;[0]),wide(264;[$base,$inh])];
[
  (v(1;"args_sizes_get.two";["Wf:30-35","p1:1214-1230"];
    [step("args_sizes_get";[32,36];0;[cell(32;[2,5])])]) | .world.args=["p","xy"]),
  (v(2;"args_get.layout";["Wf:15-28","p1:1190-1210"];
    [step("args_get";[0,128];0;[cell(0;[128,130]),text(128;"p\u0000xy\u0000")])]) | .world.args=["p","xy"]),
  (v(4;"environ_sizes_get.two";["Wf:45-51","p1:1265-1283"];
    [step("environ_sizes_get";[32,36];0;[cell(32;[2,9])])]) | .world.env=["A=1","B=xy"]),
  (v(5;"environ_get.layout";["Wf:37-43","p1:1234-1261"];
    [step("environ_get";[0,128];0;[cell(0;[128,132]),text(128;"A=1\u0000B=xy\u0000")])]) | .world.env=["A=1","B=xy"]),
  (v(6;"clock_time_get.realtime";["Wf:61-71","U29a-v2:S3 clocks; E departures"];
    [step("clock_time_get";[0,1,40];0;[wide(40;[123456789])]) | contract])),
  (v(7;"clock_time_get.monotonic";["Wf:61-71","U29a-v2:S3 clocks; E departures"];
    [step("clock_time_get";[1,0,40];0;[wide(40;[87654321])]) | contract])),
  (v(8;"clock_time_get.process";["p1:1303-1323"];
    [step("clock_time_get";[2,0,40];8;[wide(40;[0])])])),
  (v(9;"clock_time_get.thread";["p1:1303-1323"];
    [step("clock_time_get";[3,0,40];8;[wide(40;[0])])])),
  (v(10;"clock_time_get.invalid-id";["Wt:17-31","p1:1114-1120"];
    [step("clock_time_get";[4,0,40];28;[]) | outside]) | .sources += ["LEAD-D2: invalid scalar outside profile; observed conversion trap"]),
  (v(11;"clock_time_get.misaligned";["WD:Pointers","p1:1114-1135","U29a-v2:S2 profile"];
    [{mem:[],call:"clock_time_get",args:[0,0,41],expect:{outcome:"out-of-profile",basis:"contract"}}])),
  (v(12;"fd_close.file";["Wf:97-102","p1:1357-1390"];
    [fileOpen,step("fd_close";[4];0;[]),step("fd_fdstat_get";[4,256];8;[])])),
  (v(13;"fd_close.absent";["p1:1363-1366"];
    [step("fd_close";[99];8;[])])),
  (v(14;"fd_close.preopen";["p1:1357-1390","p1:1815-1828"];
    [step("fd_close";[3];0;[]),step("fd_prestat_get";[3,256];8;[])])),
  (v(15;"fd_fdstat_get.stdio";["p1:1410-1431","U29a-v2:S1 non-tty streams"];
    [step("fd_fdstat_get";[0,256];0;fdstat(0;2;2)),
     step("fd_fdstat_get";[1,256];0;fdstat(0;64;64)),
     step("fd_fdstat_get";[2,256];0;fdstat(0;64;64))])),
  (v(16;"fd_fdstat_get.preopen";["p1:1432-1478","U29a-v2:S1 preBase/preInh; E rights departure"];
    [step("fd_fdstat_get";[3,256];0;fdstat(3;preBase;preInh)) | contract])),
  (v(17;"fd_fdstat_get.requested";["Wf:373-382","U29a-v2:S3 path_open; E rights departure"];
    [fileOpen,step("fd_fdstat_get";[4,256];0;fdstat(4;110;0)) | if .call=="fd_fdstat_get" then contract else . end])),
  (v(18;"fd_fdstat_get.absent";["p1:507-512","p1:1404-1410"];
    [step("fd_fdstat_get";[99,256];8;[])])),
  (v(19;"fd_fdstat_set_flags.append";["p1:1527-1550","p1:665-702"];
    [fileOpen,step("fd_fdstat_set_flags";[4,1];0;[]),write(4;"X"),seek(4;0;1;0;4)]) | .final.files["."].f.file.text="abcX"),
  (v(20;"fd_fdstat_set_flags.invalid-bit";["Wt:394-414","p1:1114-1120"];
    [step("fd_fdstat_set_flags";[99,32];28;[]) | outside]) | .sources += ["LEAD-D2: invalid scalar outside profile; observed conversion trap"]),
  (v(21;"fd_fdstat_set_flags.stdout";["p1:1527-1541","p1:523-532"];
    [step("fd_fdstat_set_flags";[1,1];8;[])])),
  (v(22;"fd_fdstat_set_flags.dsync";["p1:1543-1549"];
    [fileOpen,step("fd_fdstat_set_flags";[4,2];28;[])])),
  (v(23;"fd_prestat_get.preopen";["Wf:179-184","p1:1815-1828","Wt:731-760"];
    [step("fd_prestat_get";[3,256];0;[cell(256;[0,1])])])),
  (v(24;"fd_prestat_get.stdout";["p1:1815-1828"];
    [step("fd_prestat_get";[1,256];8;[])])),
  (v(25;"fd_prestat_dir_name.preopen";["p1:1833-1856"];
    [step("fd_prestat_dir_name";[3,256,1];0;[text(256;".")])])),
  (v(26;"fd_prestat_dir_name.short";["p1:1847-1849"];
    [step("fd_prestat_dir_name";[3,256,0];37;[])])),
  (v(27;"fd_prestat_dir_name.stdout";["p1:1855","probe c13:prestat_stdout"];
    [step("fd_prestat_dir_name";[1,256,1];54;[])])),
  (v(28;"fd_prestat_dir_name.absent";["p1:507-512","p1:1843"];
    [step("fd_prestat_dir_name";[99,256,1];8;[])])),
  (v(29;"fd_read.file";["Wf:211-220","p1:1665-1722"];
    [fileOpen,read(4;8;"abc"),seek(4;0;1;0;3)])),
  (v(30;"fd_read.eof";["p1:1683-1722"];
    [fileOpen,seek(4;3;0;0;3),read(4;8;"")])),
  (v(31;"fd_read.first-buffer";["p1:184-224","p1:1672"];
    [fileOpen,step("fd_read";[4,0,2,32];0;[cell(32;[2]),text(256;"ab"),hex(320;"00000000")])
     | if .call=="fd_read" then init([cell(0;[256,2,320,4])]) else . end])),
  (v(32;"fd_read.skip-empty";["p1:207-224"];
    [fileOpen,step("fd_read";[4,0,3,32];0;[cell(32;[2]),text(320;"ab"),hex(384;"00")])
     | if .call=="fd_read" then init([cell(0;[256,0,320,2,384,1])]) else . end])),
  (v(33;"fd_read.stdin-chunk";["p1:1724-1737","probe stdin-chunk","U29a-v2:S3 transfer cap"];
    [step("fd_read";[0,0,1,32];0;[cell(32;[65536]),text(1024;("x"*65536)),hex(66560;"00")])
     | init([cell(0;[1024,70000])])]) | .world.stdin.text=("x"*70000) | .pages=2),
  (v(34;"fd_read.stdin-empty";["p1:1724-1737"];
    [read(0;8;"")])),
  (v(35;"fd_read.stdout";["p1:1738"];
    [step("fd_read";[1,0,1,32];8;[cell(32;[0])]) | init([cell(0;[256,8])])])),
  (v(36;"fd_read.directory";["p1:1738"];
    [step("fd_read";[3,0,1,32];8;[cell(32;[0])]) | init([cell(0;[256,8])])])),
  (v(37;"fd_write.first-buffer";["Wf:288-301","p1:184-204","p1:706-723"];
    [step("fd_write";[1,0,2,32];0;[cell(32;[1])]) | init([cell(0;[256,1,257,1]),text(256;"AB")])]) | .final.stdout.text="A"),
  (v(38;"fd_write.offset";["p1:665-702"];
    [fileOpen,seek(4;1;0;0;1),write(4;"XY"),seek(4;0;1;0;3)]) | .final.files["."].f.file.text="aXY"),
  (v(39;"fd_write.append-after-seek";["p1:665-702"];
    [open("f";0;110;0;1;0;4),seek(4;0;0;0;0),write(4;"Z"),seek(4;0;1;0;4)]) | .final.files["."].f.file.text="abcZ"),
  (v(40;"fd_write.gap";["p1:665-702","U29a-v2:S3 file write gaps"];
    [fileOpen,seek(4;5;0;0;5),write(4;"Z"),seek(4;0;1;0;6)]) | .final.files["."].f.file={hex:"61626300005a"}),
  (v(41;"fd_write.stdin";["p1:724"];
    [step("fd_write";[0,0,1,32];8;[cell(32;[0])]) | init([cell(0;[256,1]),text(256;"A")])])),
  (v(42;"fd_write.directory";["p1:724"];
    [step("fd_write";[3,0,1,32];8;[cell(32;[0])]) | init([cell(0;[256,1]),text(256;"A")])])),
  (v(43;"fd_write.empty";["p1:184-204"];
    [step("fd_write";[1,0,2,32];0;[cell(32;[0])]) | init([cell(0;[256,0,320,0])])])),
  (v(44;"fd_write.overlap";["U29a-v2:S2 profile disjointness"];
    [{mem:[cell(0;[256,1]),text(256;"A")],call:"fd_write",args:[1,0,1,256],expect:{outcome:"out-of-profile",basis:"contract"}}])),
  (v(45;"fd_write.oob-tail";["p1:184-204","probe c13:write_tail_oob","U29a-v2:S2 maximal regions"];
    [{mem:[cell(0;[256,1,65536,1]),text(256;"A")],call:"fd_write",args:[1,0,2,32],expect:{outcome:"out-of-profile",basis:"contract"}}])),
  (v(46;"fd_seek.bases";["Wf:262-275","p1:1889-1921"];
    [fileOpen,seek(4;1;0;0;1),seek(4;1;1;0;2),seek(4;-1;2;0;2)])),
  (v(47;"fd_seek.negative-set";["p1:1905-1920"];
    [fileOpen,seek(4;-1;0;28;0)])),
  (v(48;"fd_seek.u64-overflow";["p1:1908-1912"];
    [fileOpen,seek(4;"9223372036854775807";0;0;"9223372036854775807"),
     seek(4;"9223372036854775807";1;0;"18446744073709551614"),seek(4;2;1;28;"18446744073709551614")])),
  (v(49;"fd_seek.invalid-whence";["Wt:330-341","p1:1114-1120"];
    [seek(99;0;3;28;0) | outside]) | .sources += ["LEAD-D2: invalid scalar outside profile; observed conversion trap"]),
  (v(50;"fd_seek.stdout";["p1:534-546"];
    [seek(1;0;0;70;0)])),
  (v(51;"fd_seek.directory";["p1:534-546"];
    [seek(3;0;0;8;0)])),
  (v(52;"fd_seek.absent";["p1:534-546"];
    [seek(99;0;0;8;0)])),
  (v(53;"path_open.create";["Wf:364-389","p1:2156-2220"];
    [open("new";1;110;0;0;0;4)]) | .final.files["."].new={file:{text:""}}),
  (v(54;"path_open.existing";["p1:2156-2220"];
    [open("f";0;2;0;0;0;4),read(4;3;"abc")])),
  (v(55;"path_open.exclusive-create";["Wt:455-465","U29a-v2:S3 path_open"];
    [open("f";5;110;0;0;20;0)])),
  (v(56;"path_open.excl-without-create";["probe c13:open_excl_existing","U29a-v2:S3 path_open"];
    [open("f";4;2;0;0;0;4)])),
  (v(57;"path_open.truncate";["Wt:455-465","p1:2156-2220"];
    [open("f";8;110;0;0;0;4),read(4;3;"")]) | .final.files["."].f.file.text=""),
  (v(58;"path_open.libc-create-truncate";["Wt:197-262","U29a-v2:S1 preBase includes path_filestat_set_size","U29a-v2:T5 libc-shaped open"];
    [open("f";9;wr;0;0;0;4)]) | .final.files["."].f.file.text=""),
  (v(59;"path_open.directory-on-file";["Wt:455-465","U29a-v2:S3 path_open"];
    [open("f";2;2;0;0;54;0)])),
  (v(60;"path_open.file-slash";["U29a-v2:S3 path walk trailing slash"];
    [open("f/";0;2;0;0;54;0)])),
  (v(61;"path_open.create-slash";["probe c13:open_create_trailing","U29a-v2:S3 path_open"];
    [open("newfile/";1;64;0;0;31;0)])),
  (v(62;"path_open.write-directory";["U29a-v2:S3 path_open"];
    [open("d";0;64;0;0;31;0)])),
  (v(63;"path_open.read-directory";["U29a-v2:S3 path_open"];
    [open("d";2;2;0;0;0;4)])),
  (v(64;"path_open.directory-create";["U29a-v2:S3 path_open argument checks"];
    [open("new";3;2;0;0;28;0)])),
  (v(65;"path_open.missing";["U29a-v2:S3 path_open"];
    [open("missing";0;2;0;0;44;0)])),
  (v(66;"path_open.missing-parent";["U29a-v2:S3 typed path walk"];
    [open("missing/new";1;64;0;0;44;0)])),
  (v(67;"path_open.file-parent";["U29a-v2:S3 typed path walk"];
    [open("f/new";1;64;0;0;54;0)])),
  (v(68;"path_open.file-dotdot";["probe c13:open_file_dotdot","U29a-v2:S3 typed path walk"];
    [open("f/..";0;2;0;0;54;0)])),
  (v(69;"path_open.escape";["U29a-v2:S3 path confinement"];
    [open("..";0;2;0;0;63;0)])),
  (v(70;"path_open.absolute";["U29a-v2:S3 path confinement"];
    [open("/f";0;2;0;0;63;0)])),
  (v(71;"path_open.empty";["U29a-v2:S3 path walk"];
    [open("";0;2;0;0;44;0)])),
  (v(72;"path_open.nul";["probe c13:open_nul","U29a-v2:S3 NUL path"];
    [open("nul\u0000name";1;64;0;0;28;0)])),
  (v(73;"path_open.file-dirfd";["p1:2188-2194"];
    [fileOpen,(open("x";0;2;0;0;54;0) | .args[0]=4 | .mem += [cell(32;[0])])])),
  (v(74;"path_open.stdout-dirfd";["p1:2188-2194"];
    [open("f";0;2;0;0;8;0) | .args[0]=1])),
  (v(75;"path_open.inheriting-rights";["Wf:373-382","U29a-v2:S3 rights subset; E rights departure"];
    [open("f";0;536870914;0;0;76;0) | contract])),
  (v(76;"path_open.invalid-oflags";["Wt:455-465","p1:1114-1120"];
    [open("f";16;2;0;0;28;0) | outside]) | .sources += ["LEAD-D2: invalid scalar outside profile; observed conversion trap"]),
  (v(77;"path_open.reuse";["p1:440-465","p1:1366","probe fd-reuse"];
    [fileOpen,open("f";0;110;0;0;0;5),open("f";0;110;0;0;0;6),
     step("fd_close";[4];0;[]),step("fd_close";[6];0;[]),
     open("f";0;110;0;0;0;6),open("f";0;110;0;0;0;4)])),
  (v(78;"path_open.independent-offsets";["p1:2208-2213","p1:1680-1722"];
    [fileOpen,open("f";0;110;0;0;0;5),read(4;1;"a"),read(5;2;"ab"),read(4;2;"bc")])),
  (v(79;"path_create_directory.new";["Wf:302-310","p1:2038-2050"];
    [path("path_create_directory";"newdir";0)]) | .final.files["."].newdir={dir:{}}),
  (v(80;"path_create_directory.exists";["p1:2038-2050","U29a-v2:S3 mkdir"];
    [path("path_create_directory";"d";20)])),
  (v(81;"path_create_directory.slash";["probe c13:mkdir_trailing","U29a-v2:S3 mkdir"];
    [path("path_create_directory";"newdir/";0)]) | .final.files["."].newdir={dir:{}}),
  (v(82;"path_create_directory.missing-parent";["U29a-v2:S3 typed walk"];
    [path("path_create_directory";"missing/new";44)])),
  (v(83;"path_create_directory.file-dirfd";["p1:567-573","p1:2044"];
    [fileOpen,(path("path_create_directory";"new";8) | .args[0]=4)])),
  (v(84;"path_remove_directory.empty";["Wf:403-412","p1:2242-2253"];
    [path("path_remove_directory";"d";0)]) | del(.final.files["."].d)),
  (v(85;"path_remove_directory.nonempty";["Wf:404","U29a-v2:S3 rmdir"];
    [path("path_remove_directory";"d";55)]) | .world.dirs[0].tree.d.dir.k={file:{text:"x"}} | .final.files["."]=.world.dirs[0].tree),
  (v(86;"path_remove_directory.file";["U29a-v2:S3 rmdir"];
    [path("path_remove_directory";"f";54)])),
  (v(87;"path_remove_directory.missing";["U29a-v2:S3 rmdir"];
    [path("path_remove_directory";"missing";44)])),
  (v(88;"path_remove_directory.dot";["probe c13:rmdir_dot","U29a-v2:S3 rmdir"];
    [path("path_remove_directory";"d/.";28)])),
  (v(89;"path_remove_directory.dotdot";["LEAD-D2: rmdir last .. inval; observed probe"];
    [path("path_remove_directory";"d/..";28)])),
  (v(90;"path_unlink_file.file";["Wf:438-447","p1:2293-2306"];
    [path("path_unlink_file";"f";0)]) | del(.final.files["."].f)),
  (v(91;"path_unlink_file.directory";["Wf:438-440"];
    [path("path_unlink_file";"d";31)])),
  (v(92;"path_unlink_file.directory-slash";["Wf:438-440","probe c13:unlink_dir_slash"];
    [path("path_unlink_file";"d/";31)])),
  (v(93;"path_unlink_file.file-slash";["U29a-v2:S3 unlink trailing slash"];
    [path("path_unlink_file";"f/";54)])),
  (v(94;"path_unlink_file.missing";["U29a-v2:S3 unlink"];
    [path("path_unlink_file";"missing";44)])),
  (v(95;"path_unlink_file.open-identity";["U29a-v2:S1 node identity; S3 unlink"];
    [fileOpen,path("path_unlink_file";"f";0),read(4;3;"abc")]) | del(.final.files["."].f)),
  (v(96;"path_unlink_file.recreate";["U29a-v2:S1 node identity; S3 unlink"];
    [fileOpen,path("path_unlink_file";"f";0),open("f";1;110;0;0;0;5),read(5;3;""),read(4;3;"abc")]) | .final.files["."].f.file.text=""),
  (v(97;"path_filestat_get.file";["Wf:313-324","p1:2055-2097","U29a-v2:S1 depth-first ino; S3 stat; E metadata departure"];
    [stat("f";0;0;[wide(256;[1,2]),cell(272;[4]),wide(280;[1,3,0,0,0])]) | contract]) | del(.world.dirs[0].tree.d,.final.files["."].d)),
  (v(98;"path_filestat_get.directory";["Wf:313-324","p1:2055-2097","U29a-v2:S1 depth-first ino; S3 stat; E metadata departure"];
    [stat("d";0;0;[wide(256;[1,2]),cell(272;[3]),wide(280;[1,0,0,0,0])]) | contract]) | del(.world.dirs[0].tree.f,.final.files["."].f)),
  (v(99;"path_filestat_get.missing";["U29a-v2:S3 stat"];
    [stat("missing";0;44;[])])),
  (v(100;"path_filestat_get.file-slash";["U29a-v2:S3 typed path walk"];
    [stat("f/";0;54;[])])),
  (v(101;"path_filestat_get.invalid-lookupflags";["Wt:445-452","p1:1114-1120"];
    [stat("f";2;28;[]) | outside]) | .sources += ["LEAD-D2: invalid scalar outside profile; observed conversion trap"]),
  (v(102;"proc_exit.zero";["Wf:461-470","p1:2597-2607"];
    [{mem:[],call:"proc_exit",args:[0],expect:{outcome:"exit",code:0,basis:"wasmtime"}}]) | .final.exited=0),
  (v(103;"proc_exit.three";["Wf:461-470","p1:2597-2607"];
    [{mem:[],call:"proc_exit",args:[3],expect:{outcome:"exit",code:3,basis:"wasmtime"}}]) | .final.exited=3),
  (v(104;"random_get.two";["Wf:484-494","p1:2625-2640"];
    [{mem:[hex(255;"aa0000bb")],call:"random_get",args:[256,2],expect:{outcome:"any-bytes",errno:0,length:2,basis:"wasmtime"}}])),
  (v(105;"random_get.empty";["Wf:484-494","p1:2625-2640"];
    [step("random_get";[256,0];0;[hex(256;"00")])]))
] + [
  (v(106;"fd_read.stdin-zero-buffer";["LEAD-D1: stdin empty buffers intr","p1:276-287","probe stdin-zero:readzero"];
    [step("fd_read";[0,0,1,32];27;[cell(32;[4660])]) | init([cell(0;[256,0]),cell(32;[4660])])])),
  (v(107;"fd_read.stdin-zero-table";["LEAD-D1: stdin empty buffers intr","p1:276-287","probe stdin-zero:readnone"];
    [step("fd_read";[0,0,0,32];27;[cell(32;[4660])]) | init([cell(32;[4660])])]) | .world.stdin.text="data"),
  (v(108;"fd_read.file-zero-buffer";["p1:1680-1722","LEAD-D1: regular-file empty read"];
    [fileOpen,seek(4;2;0;0;2),read(4;0;""),seek(4;0;1;0;2)])),
  (v(109;"fd_read.file-zero-past-eof";["p1:1680-1722","U29a-v2:T5 zero-byte IO"];
    [fileOpen,seek(4;5;0;0;5),read(4;0;""),seek(4;0;1;0;5)])),
  (v(110;"fd_write.zero-past-eof";["p1:665-702","U29a-v2:T5 zero-byte IO"];
    [fileOpen,seek(4;5;0;0;5),write(4;""),seek(4;0;1;0;5)])),
  (v(111;"fd_write.skip-empty";["p1:184-204"];
    [step("fd_write";[1,0,3,32];0;[cell(32;[1])]) | init([cell(0;[256,0,320,1,384,1]),text(320;"B"),text(384;"C")])]) | .final.stdout.text="B"),
  (v(112;"fd_write.stderr";["p1:706-723"];
    [write(2;"E")]) | .final.stderr.text="E"),
  (v(113;"fd_write.absent";["p1:507-512","p1:626-640"];
    [step("fd_write";[99,0,1,32];8;[cell(32;[4660])]) | init([cell(0;[256,1]),text(256;"A"),cell(32;[4660])])])),
  (v(114;"fd_read.absent";["p1:507-512","p1:1672-1674"];
    [step("fd_read";[99,0,1,32];8;[cell(32;[4660])]) | init([cell(0;[256,1]),cell(32;[4660])])])),
  (v(115;"fd_fdstat_set_flags.absent";["p1:523-532","p1:1527-1541"];
    [step("fd_fdstat_set_flags";[99,1];8;[])])),
  (v(116;"fd_fdstat_set_flags.directory";["p1:523-532","p1:1527-1541"];
    [step("fd_fdstat_set_flags";[3,1];8;[])])),
  (v(117;"fd_fdstat_set_flags.sync-rsync";["p1:1543-1549"];
    [fileOpen,step("fd_fdstat_set_flags";[4,16];28;[]),step("fd_fdstat_set_flags";[4,8];28;[])])),
  (v(118;"fd_fdstat_set_flags.clear";["p1:1543-1552","p1:1506-1521"];
    [fileOpen,step("fd_fdstat_set_flags";[4,5];0;[]),step("fd_fdstat_get";[4,512];0;[cell(512;[327684])]),
     step("fd_fdstat_set_flags";[4,0];0;[]),step("fd_fdstat_get";[4,512];0;[cell(512;[4])]),write(4;"X")]) | .final.files["."].f.file.text="Xbc"),
  (v(119;"fd_read.missing-right";["Wt:202-207","U29a-v2:S3 E rights enforcement"];
    [open("f";0;64;0;0;0;4),(step("fd_read";[4,0,1,32];76;[cell(32;[4660])]) | contract | init([cell(0;[256,1]),cell(32;[4660])]))])),
  (v(120;"fd_write.missing-right";["Wt:221-224","U29a-v2:S3 E rights enforcement"];
    [open("f";0;2;0;0;0;4),(step("fd_write";[4,0,1,32];76;[cell(32;[4660])]) | contract | init([cell(0;[256,1]),text(256;"X"),cell(32;[4660])]))])),
  (v(121;"fd_seek.missing-right";["Wt:208-219","U29a-v2:S3 E rights enforcement"];
    [open("f";0;2;0;0;0;4),(seek(4;1;0;76;0)|contract)])),
  (v(122;"fd_fdstat_set_flags.missing-right";["Wt:210-211","U29a-v2:S3 E rights enforcement"];
    [open("f";0;2;0;0;0;4),(step("fd_fdstat_set_flags";[4,1];76;[])|contract)])),
  (v(123;"fd_seek.seek-implies-tell";["Wt:208-209","U29a-v2:S3 fd_seek right"];
    [open("f";0;4;0;0;0;4),seek(4;0;1;0;0)])),
  (v(124;"fd_seek.tell-only";["Wt:216-219","U29a-v2:S3 fd_seek right"];
    [open("f";0;32;0;0;0;4),seek(4;0;1;0;0),(seek(4;1;1;76;0)|contract)])),
  (v(125;"fd_seek.cur-underflow";["p1:1908-1912"];
    [fileOpen,seek(4;-1;1;28;0)])),
  (v(126;"fd_seek.end-underflow";["p1:1913-1916"];
    [fileOpen,seek(4;-4;2;28;0)])),
  (v(127;"fd_seek.min-i64";["p1:1905-1920"];
    [fileOpen,seek(4;"-9223372036854775808";0;28;0)])),
  (v(128;"fd_write.file-size-limit";["LEAD-D1: file limit 2^63-1","U29a-v2:S3 file room completion"];
    [fileOpen,seek(4;"9223372036854775807";0;0;"9223372036854775807"),
     (step("fd_write";[4,0,1,32];28;[cell(32;[4660])])|init([cell(0;[256,1]),text(256;"X"),cell(32;[4660])]))])),
  (v(129;"path_open.truncate-open-node";["U29a-v2:S1 file identity","p1:2208-2213"];
    [fileOpen,seek(4;1;0;0;1),open("f";8;110;0;0;0;5),read(4;2;"")]) | .final.files["."].f.file.text=""),
  (v(130;"path_unlink_file.old-new-writes";["U29a-v2:S1 file identity; S3 unlink"];
    [fileOpen,path("path_unlink_file";"f";0),open("f";1;110;0;0;0;5),write(5;"N"),write(4;"O"),seek(4;0;0;0;0),read(4;3;"Obc")]) | .final.files["."].f.file.text="N"),
  (v(131;"path_open.normalized";["U29a-v2:S3 typed walk"];
    [open("./d/../f";0;2;0;0;0;4),read(4;3;"abc")])),
  (v(132;"path_open.dirfd-confinement";["U29a-v2:S3 typed walk confinement"];
    [open("d";2;8192;110;0;0;4),(open("../f";0;2;0;0;63;0)|.args[0]=4|.mem+=[cell(32;[0])])])),
  (v(133;"path_open.non-utf8";["p1:1132 invalid UTF8 ilseq","LEAD-D1: E opaque byte paths"];
    [open("x";0;2;0;0;44;0)|contract|init([hex(128;"ff")])])),
  (v(134;"path_create_directory.absent-dirfd";["p1:567-573","p1:2044"];
    [path("path_create_directory";"new";8)|.args[0]=99])),
  (v(135;"path_remove_directory.file-dirfd";["p1:567-573","p1:2248"];
    [fileOpen,(path("path_remove_directory";"d";8)|.args[0]=4)])),
  (v(136;"path_unlink_file.file-dirfd";["p1:567-573","p1:2299"];
    [fileOpen,(path("path_unlink_file";"f";8)|.args[0]=4)])),
  (v(137;"path_filestat_get.file-dirfd";["p1:567-573","p1:2063"];
    [fileOpen,(stat("f";0;8;[])|.args[0]=4)])),
  (v(138;"fd_prestat_get.absent";["p1:507-512","p1:1824"];
    [step("fd_prestat_get";[99,256];8;[])])),
  (v(139;"fd_prestat_dir_name.opened-directory";["p1:1833-1856"];
    [open("d";2;2;0;0;0;4),step("fd_prestat_dir_name";[4,256,1];54;[])])),
  (v(140;"path_create_directory.file-exists";["U29a-v2:S3 mkdir exists"];
    [path("path_create_directory";"f";20)])),
  (v(141;"path_open.invalid-rights";["LEAD-D2: invalid right bit >=30 outside profile"];
    [open("f";0;1073741824;0;0;28;0)|outside])),
  (v(142;"path_open.invalid-fdflags";["LEAD-D2: invalid flags outside profile"];
    [open("f";0;2;0;32;28;0)|outside])),
  (v(143;"path_open.invalid-lookupflags";["LEAD-D2: invalid flags outside profile"];
    [open("f";0;2;0;0;28;0)|.args[1]=2|outside])),
  (v(144;"fd_fdstat_get.padding";["Wt:416-428 fdstat fields","WD:Pointers","p1:1410-1421"];
    [step("fd_fdstat_get";[0,256];0;[hex(256;"00aa0000aaaaaaaa02000000000000000200000000000000")])
     |init([hex(256;("aa"*24))])])),
  (v(145;"fd_prestat_get.padding";["Wt:731-760 prestat fields","p1:1815-1828"];
    [step("fd_prestat_get";[3,256];0;[hex(256;"00aaaaaa01000000")])|init([hex(256;("aa"*8))])])),
  (v(146;"path_filestat_get.follow";["Wt:445-452 lookupflags","p1:2055-2097"];
    [stat("f";1;0;[wide(256;[1]),cell(272;[4]),wide(288;[3])])])),
  (v(147;"path_filestat_get.directory-type";["p1:2055-2097"];
    [stat("d";0;0;[wide(256;[1]),cell(272;[3])])]))
] + [
  range(1;7) as $n |
  ([range(0;$n)|if .%3==0 then "" elif .%3==1 then "ab" else "α" end]) as $args |
  ($args|map(utf8bytelength+1)|add) as $len |
  (reduce $args[] as $a ({ptr:128,ptrs:[]};.ptrs += [.ptr]|.ptr+=($a|utf8bytelength)+1)|.ptrs) as $ptrs |
  v(148+$n-1;("args_get.property-layout-"+($n|tostring));["Wf:15-35","p1:1190-1230","property: count; sum(lenUTF8+1); pointer prefix sums; joined NUL bytes; guards"];
    [step("args_sizes_get";[32,36];0;[cell(32;[$n,$len])]),
     (step("args_get";[0,128];0;[cell(0;$ptrs),text(128;($args|map(.+"\u0000")|join(""))),hex(127;"aa"),hex(128+$len;"bb")])
       |init([hex(127;"aa"),hex(128+$len;"bb")]))]) | .world.args=$args
] + [
  [0,1,3,5] | to_entries[] as $a | [0,1,4] | to_entries[] as $b |
  (if $a.value>0 then $a.value else $b.value end) as $first |
  ([3,$first]|min) as $count |
  v(154+3*$a.key+$b.key;("fd_read.property-prefix-"+($a.value|tostring)+"-"+($b.value|tostring));
    ["p1:207-224","p1:1680-1722","property: first nonempty iovec only; file prefix; later bytes unchanged"];
    [fileOpen,(step("fd_read";[4,0,2,32];0;
       [cell(32;[$count]),text(256;(if $a.value>0 then "abc"[0:$count] else "" end)),
        text(320;(if $a.value==0 then "abc"[0:$count] else "" end)),
        hex(256+$count;(if $a.value>0 then "00" else "" end)),
        hex(320;(if $a.value>0 then "00" else "" end))])
       |init([cell(0;[256,$a.value,320,$b.value])])),seek(4;0;1;0;$count)])
]
+ [
  (v(166;"path_open.directory-append";["p1:1472 directory descriptors store no fdflags","probe r5 OpenFlags"];
    [open("d";0;2;0;1;0;4),step("fd_fdstat_get";[4,256];0;[cell(256;[3])])])),
  (v(167;"path_open.directory-nonblock";["p1:1472","probe r5 OpenFlags"];
    [open("d";0;2;0;4;0;4),step("fd_fdstat_get";[4,256];0;[cell(256;[3])])])),
  (v(168;"path_open.dsync";["p1:2176-2183 sync flags unsupported","probe r5 OpenFlags"];[open("f";0;110;0;2;58;0)])),
  (v(169;"path_open.rsync";["p1:2176-2183","probe r5 OpenFlags"];[open("f";0;110;0;8;58;0)])),
  (v(170;"path_open.sync";["p1:2176-2183","probe r5 OpenFlags"];[open("f";0;110;0;16;58;0)])),
  (v(171;"path_open.directory-sync";["p1:2176-2183","probe r5 OpenFlags"];[open("d";0;2;0;16;58;0)])),
  (v(172;"fd_read.offset-limit";["p1:1689-1707 pread","Linux rw_verify_area: pos + count >= 2^63 -> EINVAL","probe r5 OffsetIO"];
    [fileOpen,seek(4;"9223372036854775807";0;0;"9223372036854775807"),
     (step("fd_read";[4,0,1,32];28;[cell(32;[4660])])|init([cell(0;[256,1]),cell(32;[4660])]))])),
  (v(173;"fd_read.zero-past-limit";["p1:1689-1707 pread","Linux rw_verify_area: pos < 0 -> EINVAL","probe r5 OffsetIO"];
    [fileOpen,seek(4;"9223372036854775807";0;0;"9223372036854775807"),seek(4;1;1;0;"9223372036854775808"),
     (step("fd_read";[4,0,1,32];28;[cell(32;[4660])])|init([cell(0;[256,0]),cell(32;[4660])]))])),
  (v(174;"fd_write.zero-past-limit";["p1:654-655 pwrite","Linux rw_verify_area: pos < 0 -> EINVAL","probe r5 OffsetIO"];
    [fileOpen,seek(4;"9223372036854775807";0;0;"9223372036854775807"),seek(4;1;1;0;"9223372036854775808"),
     (step("fd_write";[4,0,1,32];28;[cell(32;[4660])])|init([cell(0;[256,0]),cell(32;[4660])]))])),
  (v(175;"fd_write.crossing-limit";["p1:654-655 pwrite","Linux rw_verify_area: pos + count >= 2^63 -> EINVAL","probe MAIN Append"];
    [fileOpen,seek(4;"9223372036854775805";0;0;"9223372036854775805"),
     (step("fd_write";[4,0,1,32];28;[cell(32;[4660])])|init([cell(0;[256,3]),text(256;"XYZ"),cell(32;[4660])]))])),
  (v(176;"path_open.removed-parent";["POSIX rmdir: no new entries in a removed directory","probe r5 UnlinkedDirectory"];
    [open("e";0;9728;66;0;0;4),path("path_remove_directory";"e";0),
     (step("path_open";[4,0,128,5,1,0,0,0,36];44;[cell(36;[4660])])|init([text(128;"child"),cell(36;[4660])])),
     (step("path_create_directory";[4,128,4];44;[])|init([text(128;"hild")]))]) | .world.dirs[0].tree.e={dir:{}}),
  (v(177;"environ_get.memory-end";["p1:1171,1177,1249 one-past-end pointer advance","probe r5 MemoryEnd"];
    [step("environ_get";[0,4294967292];0;[])|outside]) | .world.env=["K=V"] | .pages=65536),
  (v(178;"environ_get.memory-end-control";["p1:1240-1256","probe r5 MemoryEnd"];
    [step("environ_get";[0,4294967291];0;[cell(0;[4294967291]),text(4294967291;"K=V\u0000")])]) | .world.env=["K=V"] | .pages=65536),
  (v(179;"fd_prestat_dir_name.memory-end";["p1:1171,1849","probe r5 MemoryEnd"];
    [step("fd_prestat_dir_name";[3,4294967295,1];0;[])|outside]) | .pages=65536),
  (v(180;"fd_prestat_dir_name.memory-end-control";["p1:1840-1852","probe r5 MemoryEnd"];
    [step("fd_prestat_dir_name";[3,4294967294,1];0;[text(4294967294;".")])]) | .pages=65536),
  (v(181;"random_get.memory-end";["p1:1171,2637","probe r5 MemoryEnd"];
    [step("random_get";[4294967295,1];0;[])|outside]) | .pages=65536),
  (v(182;"random_get.memory-end-control";["p1:2630-2640","probe r5 MemoryEnd"];
    [step("random_get";[4294967294,1];0;[])]) | .pages=65536)
]
