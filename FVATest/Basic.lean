import FVA.Cli

/-! Compile-time checks: a failing `#guard` fails `lake build FVATest`, so `lake test` fails too. -/

#guard FVA.Cli.dispatch ["version"] == { out := s!"fva {FVA.version}\n" }
#guard (FVA.Cli.dispatch ["frobnicate"]).code == 2
#guard (FVA.Cli.dispatch []).out == FVA.Cli.helpText
