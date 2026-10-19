Proved R1–R3 for all inputs in Lean 4. All six kernel checkers passed; the C rebuild matches the shipped binary.

See [VERIFICATION.md](/tmp/fva-bench/fva-sat_add/prototype/fva/examples/sat_add/VERIFICATION.md) for proof details, commands, and limitations—including FVA’s sandbox-blocked replay wrapper.

Recheck with:

```sh
cd prototype/fva/examples/sat_add
sh check-proofs.sh
```