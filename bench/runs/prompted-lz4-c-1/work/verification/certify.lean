/- Untrusted certificate producer. Every generated step equation is checked by kernels. -/
import Proofs.Cases
import Proofs.Composition
import Lean
open Wasm Verification

def ns (n : Nat) : String := toString n
def listNat (xs : List Nat) : String := "[" ++ String.intercalate "," (xs.map ns) ++ "]"
def labelsText (xs : List Label) : String :=
  "[" ++ String.intercalate "," (xs.map fun l =>
    "⟨"++ns l.start++","++ns l.finish++","++ns l.height++","++toString l.loop++"⟩") ++ "]"
def callsText (xs : List Activation) : String :=
  "[" ++ String.intercalate "," (xs.map fun a =>
    "⟨"++ns a.fn++","++ns a.pc++","++listNat a.locals++","++listNat a.stack++","++labelsText a.labels++"⟩") ++ "]"
def stateText (s : State) (mem trace : String) : String :=
  "{ fn := "++ns s.fn++", pc := "++ns s.pc++", locals := "++listNat s.locals++
  ", stack := "++listNat s.stack++", labels := "++labelsText s.labels++
  ", calls := "++callsText s.calls++", mem := "++mem++", trace := "++trace++" }"

def main : IO Unit := do
  let mut text := "-- Generated proof certificates; no generated declaration is trusted.\nimport Proofs.Cases\nimport Proofs.Composition\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Certificates\nopen Wasm Verification\n"
  let mut allProofs : List String := []
  for idx in List.range cases.length do
    let some c := cases[idx]? | throw (IO.userError "missing case")
    let caseName := "c"++ns idx++"_"
    let mut s := start Artifact.functions (initial c) c.src c.dst c.input.length c.cap
    let mut mem := "initial testcase"
    let mut trace := "([] : List Access)"
    let mut count := 0
    let mut accessCount := 0
    let mut marks : List Nat := [0]
    text := text ++ "namespace C"++ns idx++"\ndef testcase : Case := "++
      "⟨"++listNat c.input++","++ns c.cap++","++ns c.expected++","++ns c.src++","++ns c.dst++","++ns c.fill++"⟩\n"
    text := text ++ "def s0 : State := start Artifact.functions (initial testcase) "++
      ns c.src++" "++ns c.dst++" "++ns c.input.length++" "++ns c.cap++"\n"
    let mut result : Option Nat := none
    for _ in List.range 1000 do
      match step Artifact.functions s with
      | none => throw (IO.userError (caseName++"trapped"))
      | some (.done v _) =>
        result := some v
        break
      | some (.next t) =>
        if t.trace.length != s.trace.length then
          let some a := t.trace.head? | throw (IO.userError "trace missing")
          accessCount := accessCount+1
          if a.write then
            let some value := s.stack.head? | throw (IO.userError "store has no value")
            let name := "m"++ns accessCount
            text := text ++ "def "++name++" : Mem := store ("++mem++") "++ns a.address++" "++ns value++" "++ns a.width++"\n"
            mem := name
          let name := "t"++ns accessCount
          text := text ++ "def "++name++" : List Access := ⟨"++toString a.write++","++ns a.address++","++ns a.width++"⟩::"++trace++"\n"
          trace := name
        s := t
        count := count+1
        if count % 8 == 0 then
          text := text ++ "def s"++ns count++" : State := "++stateText s mem trace++"\n"
          marks := marks ++ [count]
    let some r := result | throw (IO.userError (caseName++"fuel exhausted"))
    if count % 8 != 0 then
      text := text ++ "def s"++ns count++" : State := "++stateText s mem trace++"\n"
      marks := marks ++ [count]
    for (lo,hi) in marks.zip marks.tail do
      text := text ++ "theorem a"++ns lo++" : advance Artifact.functions "++ns (hi-lo)++" s"++ns lo++" = some s"++ns hi++" := by rfl\n"
    text := text ++ "theorem execution : execute testcase = some ("++ns r++",s"++ns count++") := by\n"
    text := text ++ "  change run Artifact.functions 1000 s0 = some ("++ns r++",s"++ns count++")\n"
    text := text ++ "  have h"++ns count++" : run Artifact.functions "++ns (1000-count)++" s"++ns count++" = some ("++ns r++",s"++ns count++") := by rfl\n"
    for (lo,hi) in (marks.zip marks.tail).reverse do
      text := text ++ "  have h"++ns lo++" : run Artifact.functions "++ns (1000-lo)++" s"++ns lo++" = some ("++ns r++",s"++ns count++") :=\n"
      text := text ++ "    run_of_advance Artifact.functions "++ns (hi-lo)++" "++ns (1000-hi)++" s"++ns lo++" s"++ns hi++" ("++ns r++",s"++ns count++") a"++ns lo++" h"++ns hi++"\n"
    text := text ++ "  exact h0\n"
    text := text ++ "theorem checked : checks testcase = true := by\n  unfold checks\n  rw [execution]\n  rfl\n"
    text := text ++ "end C"++ns idx++"\n"
    allProofs := allProofs ++ ["C"++ns idx++".checked"]
    IO.eprintln (caseName++ns count++" steps, "++ns accessCount++" accesses")
  text := text ++ "theorem checked_cases : cases.all checks = true := by\n"
  let expression := (List.range cases.length).foldr (fun i acc => "(checks C"++ns i++".testcase && "++acc++")") "true"
  text := text ++ "  change "++expression++" = true\n"
  text := text ++ "  simp only ["++String.intercalate ", " allProofs++", Bool.and_self]\nend Certificates\n"
  let header := "-- Generated proof certificates; every equation is kernel checked.\nimport Proofs.Cases\nimport Proofs.Composition\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Certificates\nopen Wasm Verification\n"
  IO.FS.createDirAll "Proofs/Certificates"
  let mut imports := ""
  for i in List.range cases.length do
    let a := "namespace C"++ns i++"\n"
    let b := "end C"++ns i++"\n"
    let body := ((text.splitOn a)[1]!).splitOn b |>.head!
    IO.FS.writeFile ("Proofs/Certificates/C"++ns i++".lean") (header++a++body++b++"end Certificates\n")
    imports := imports ++ "import Proofs.Certificates.C"++ns i++"\n"
  let claim := (text.splitOn "theorem checked_cases")[1]!
  IO.FS.writeFile "Proofs/Certificates.lean" (imports++"namespace Certificates\nopen Verification\ntheorem checked_cases"++claim)
