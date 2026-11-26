include "probe";
def exact($ks): keys==($ks|sort);
def byteObject:
  type=="object" and
  ((exact(["text"]) and (.text|type=="string")) or
   (exact(["hex"]) and (.hex|type=="string" and test("^([0-9a-fA-F]{2})*$"))));
def integer: type=="number" and floor==. and .>=0;
def scalar: integer or (type=="string" and test("^-?[0-9]+$"));
def memOp:
  type=="object" and (.addr|integer) and
  (if has("text") then exact(["addr","text"]) and ({text:.text}|byteObject)
   elif has("hex") then exact(["addr","hex"]) and ({hex:.hex}|byteObject)
   elif has("u32") then exact(["addr","u32"]) and (.u32|type=="array" and all(.[];integer and .<4294967296))
   elif has("u64") then exact(["addr","u64"]) and (.u64|type=="array" and all(.[];scalar))
   else false end);
def treeValid:
  type=="object" and all(to_entries[];
    (.key!="" and .key!="." and .key!=".." and (.key|test("[/\u0000]")|not)) and
    (.value | if has("file") then exact(["file"]) and (.file|byteObject)
     elif has("dir") then exact(["dir"]) and (.dir|treeValid) else false end));
def valid:
  exact(["id","sources","world","pages","steps","final"]) and
  (.id|type=="string" and test("^[a-z_]+\\.[a-z0-9-]+$")) and
  (.sources|type=="array" and length>0 and all(.[];type=="string")) and
  (.world|exact(["args","env","stdin","clocks","dirs"]) and
    (.args|type=="array" and length>0 and all(.[];type=="string")) and
    (.env|type=="array" and all(.[];type=="string" and contains("="))) and
    (.stdin|byteObject) and (.clocks|length==4 and all(.[];scalar)) and
    (.dirs|type=="array" and all(.[];exact(["guest","tree"]) and (.guest|type=="string") and (.tree|treeValid)))) and
  (.pages|integer and .>0) and (.steps|type=="array" and length>0 and all(.[];
    exact(["mem","call","args","expect"]) and (.mem|all(.[];memOp)) and
    (.call as $c|.args|type=="array" and length==(sig($c)|length) and all(.[];scalar or (type=="number" and floor==.))) and
    (.expect.outcome!="any-bytes" or .expect.length==.args[1]) and
    (.expect|(.basis=="wasmtime" or .basis=="contract") and
      (if .outcome=="errno" then has("errno") and (.errno|integer) and all(.mem[]?;memOp)
       elif .outcome=="exit" then (.code|integer)
       elif .outcome=="any-bytes" then (.errno|integer) and (.length|integer)
       elif .outcome=="out-of-profile" then true else false end)))) and
  (.final|(.stdout|byteObject) and (.stderr|byteObject) and (.files|type=="object" and all(.[];treeValid)) and
    (if has("exited") then .exited|integer else true end));
