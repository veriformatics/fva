import FVA.Cli

/-! Compile-time checks: a failing `#guard` fails `lake build FVATest`, so `lake test` fails too. -/

#guard FVA.Cli.dispatch ["version"] == { out := s!"fva {FVA.version}\n" }
#guard (FVA.Cli.dispatch ["frobnicate"]).code == 2
#guard (FVA.Cli.dispatch []).out == FVA.Cli.helpText
-- a command with arguments shows its usage on `--help` and on wrong arguments, never
-- "unknown command"
#guard FVA.Cli.dispatch ["lift", "--help"] == { out := (FVA.Cli.usage "lift").get! }
#guard FVA.Cli.dispatch ["help", "trust"] == { out := (FVA.Cli.usage "trust").get! }
#guard (FVA.Cli.dispatch ["lift", "a.wasm"]).code == 2
#guard ((FVA.Cli.dispatch ["lift", "a.wasm"]).err.splitOn "Usage: fva lift").length == 2
#guard ((FVA.Cli.dispatch ["frobnicate", "--help"]).err.splitOn "unknown command").length == 2
#guard ["decode", "lift", "blob", "trust", "explain", "certify", "init"].all
  (FVA.Cli.usage · |>.isSome)
