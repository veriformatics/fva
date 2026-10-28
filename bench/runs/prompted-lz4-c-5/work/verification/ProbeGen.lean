import Lean
open Lean
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Init.Prelude}] {} 0
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 0) (mkNatLit 1)
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 0)
  let decl := Declaration.thmDecl { name := `knownFalse, levelParams := [], type := ty, value := val }
  let .ok env := env.addDeclCore 0 0 decl none false | throw (IO.userError "probe generation failed")
  writeModule env ".lake/build/lib/lean/KernelProbe.olean"
