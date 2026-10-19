"""`fva difftest`: run lifted Lean code (FVA semantics, Lean interpreter) + the real wasm
(wasmtime) on the same inputs; any mismatch = a defect in the trusted semantics or lifter."""

import random
import subprocess
import tempfile
from pathlib import Path

import wasmtime

from .lift import decode, ident
from .project import Project

EDGES = {"i32": [0, 1, 2, 3, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE, 7, 100],
         "i64": [0, 1, 2, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]}
BITS = {"i32": 32, "i64": 64}
FUEL = 1_000_000


def _cases(params: list[str], n: int, rng: random.Random) -> list[list[int]]:
    cases = [[EDGES[t][i % len(EDGES[t])] for t in params] for i in range(max(len(e) for e in EDGES.values()))]
    while len(cases) < n:
        cases.append([rng.choice(EDGES[t]) if rng.random() < 0.2 else
                      rng.getrandbits(rng.choice([4, 8, 16, BITS[t]])) for t in params])
    return cases


def _signed(v: int, bits: int) -> int:
    return v - (1 << bits) if v >= 1 << (bits - 1) else v


def difftest(project: Project, n: int = 200, seed: int = 0) -> dict:
    rng = random.Random(seed)
    results = []
    for l in project.lifted():
        b = project.run("lake", "build", l.module, check=False)
        if b.returncode != 0:
            results.append({"module": l.module, "wasm": str(l.wasm.relative_to(project.root)), "functions": [],
                            "cases": 0, "mismatches": [{"error": f"lake build {l.module} failed: {b.stdout[-800:]}"}]})
            continue
        data = l.wasm.read_bytes()
        store = wasmtime.Store()
        inst = wasmtime.Instance(store, wasmtime.Module(store.engine, data), [])
        funcs = decode(data)
        plan = [(f, args) for f in funcs for args in _cases(f.params, n, rng)]
        expected = []
        for f, args in plan:
            try:
                out = inst.exports(store)[f.name](store, *[_signed(a, BITS[t]) for a, t in zip(args, f.params)])
                outs = [] if out is None else out if isinstance(out, list) else [out]
                expected.append(" ".join(str(v % (1 << BITS[t])) for v, t in zip(outs, f.result_types)))
            except wasmtime.Trap:
                expected.append("trap")
        lines = [f"import {l.module}", "open FVA.Wasm",
                 "def fmt : Option (List Val) → String",
                 "  | some vs => \" \".intercalate (vs.map fun | .i32 v => toString v.toNat | .i64 v => toString v.toNat)",
                 "  | none => \"trap\""]
        chunks = [plan[i:i + 50] for i in range(0, len(plan), 50)]  # long `do` blocks hit maxRecDepth
        for k, chunk in enumerate(chunks):
            lines.append(f"def part{k} : IO Unit := do")
            for f, args in chunk:
                vals = ", ".join(f".{t} {a}#{BITS[t]}" for a, t in zip(args, f.params))
                lines.append(f"  IO.println (fmt (invoke {l.ns}.{ident(f.name)} {FUEL} [{vals}]))")
        lines.append("#eval do " + "; ".join(f"part{k}" for k in range(len(chunks))))
        with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=project.root, delete=False) as fh:
            fh.write("\n".join(lines) + "\n")
        try:
            r = project.run("lake", "env", "lean", fh.name, check=False)
        finally:
            Path(fh.name).unlink()
        got = r.stdout.split("\n")[:len(plan)]
        if r.returncode != 0 or len(got) != len(plan):
            mism = [{"error": (r.stdout + r.stderr)[-800:]}]
        else:
            mism = [{"func": f.name, "args": args, "wasmtime": e, "lean": g}
                    for (f, args), e, g in zip(plan, expected, got) if e != g]
        results.append({"module": l.module, "wasm": str(l.wasm.relative_to(project.root)),
                        "functions": [f.name for f in funcs], "cases": len(plan), "mismatches": mism})
    return {"ok": all(not x["mismatches"] for x in results), "results": results}


def render(r: dict) -> str:
    out = []
    for x in r["results"]:
        mark = "✓" if not x["mismatches"] else "✗"
        out.append(f"  {mark} {x['wasm']}: {x['cases']} cases over {', '.join(x['functions'])} — "
                   f"Lean semantics vs wasmtime: {len(x['mismatches'])} mismatch(es)")
        for m in x["mismatches"][:5]:
            out.append(f"      {m}")
    return "\n".join(out)
