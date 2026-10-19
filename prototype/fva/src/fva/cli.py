"""fva — Formally Verify Anything (prototype CLI). Agent-first: every command takes --json."""

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from . import difftest as dt
from . import trust as tr
from .lift import LiftError, to_lean
from .project import FVA_ROOT, Project

TOY_EXPORTS = ["clamp", "gcd", "sum_to"]


def _project_of(path: Path) -> Path:
    for d in [path.resolve(), *path.resolve().parents]:
        if (d / "lakefile.toml").exists():
            return d
    raise SystemExit(f"fva: no lakefile.toml above {path}")


def cmd_lift(a) -> int:
    out = Path(a.out)
    root = _project_of(out.parent)
    wasm = Path(a.wasm).resolve()
    try:
        text = to_lean(wasm.read_bytes(), a.ns, str(wasm.relative_to(root)))
    except LiftError as e:
        print(f"fva lift: {e}", file=sys.stderr)
        return 1
    out.write_text(text)
    print(json.dumps({"out": str(out), "ns": a.ns}) if a.json else f"lifted {wasm.name} → {out} ({a.ns})")
    return 0


def cmd_trust(a) -> int:
    r = tr.trust(Project(Path(a.project)), a.theorems, a.spec_module, build=not a.no_build, paranoid=a.paranoid)
    print(json.dumps(r, indent=1) if a.json else tr.render(r))
    return 0 if r["verdict"] == "PASS" else 1


def cmd_difftest(a) -> int:
    r = dt.difftest(Project(Path(a.project)), n=a.cases, seed=a.seed)
    print(json.dumps(r, indent=1) if a.json else dt.render(r))
    return 0 if r["ok"] else 1


def _rebuild_toy(toy: Path) -> dict:
    clang = shutil.which("clang")
    if not clang:
        return {"clang": None}
    with tempfile.TemporaryDirectory() as d:
        out = Path(d) / "toy.wasm"
        cmd = [clang, "--target=wasm32", "-O2", "-nostdlib", "-Wl,--no-entry", "-Wl,--strip-all",
               *[f"-Wl,--export={e}" for e in TOY_EXPORTS], "-o", str(out), str(toy / "toy.c")]
        subprocess.run(cmd, check=True)
        new = hashlib.sha256(out.read_bytes()).hexdigest()
    pinned = hashlib.sha256((toy / "toy.wasm").read_bytes()).hexdigest()
    ver = subprocess.run([clang, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    return {"clang": ver, "rebuiltSha": new, "pinnedSha": pinned, "identical": new == pinned}


def cmd_demo(a) -> int:
    ex = FVA_ROOT / "examples"
    toy, cheat = Project(ex / "toy"), Project(ex / "cheat")
    say = (lambda *_: None) if a.json else print
    say("== 1. Compile untrusted C source → wasm (the artifact FVA verifies)")
    rb = _rebuild_toy(toy.root)
    if rb["clang"]:
        say(f"  {rb['clang']}: rebuilt toy.wasm sha256 {rb['rebuiltSha'][:12]}… "
            + ("= pinned artifact" if rb["identical"] else f"≠ pinned {rb['pinnedSha'][:12]}… (proofs cover the pinned bytes)"))
    else:
        say("  clang not found; using the pinned toy.wasm")
    say("\n== 2. Differential test: FVA's Lean WASM semantics vs wasmtime on the real binary")
    d = dt.difftest(toy, n=a.cases)
    say(dt.render(d))
    say("\n== 3. Trust report: examples/toy (honest proofs)\n")
    t1 = tr.trust(toy, [], None)
    say(tr.render(t1))
    say("\n== 4. Trust report: examples/cheat (planted cheats; must FAIL)\n")
    t2 = tr.trust(cheat, [], None)
    say(tr.render(t2))
    ok = d["ok"] and t1["verdict"] == "PASS" and t2["verdict"] == "FAIL"
    if a.json:
        print(json.dumps({"ok": ok, "rebuild": rb, "difftest": d, "toy": t1, "cheat": t2}, indent=1))
    else:
        say(f"\n== Demo {'behaved as expected' if ok else 'DID NOT behave as expected'}: "
            "toy PASS, cheat FAIL, semantics agree with wasmtime")
    return 0 if ok else 1


def main() -> None:
    p = argparse.ArgumentParser(prog="fva", description=__doc__)
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("lift", help="wasm binary → Lean module over FVA's WASM semantics")
    s.add_argument("wasm"); s.add_argument("out"); s.add_argument("--ns", required=True)
    s.set_defaults(f=cmd_lift)
    s = sub.add_parser("trust", help="check proofs, audit axioms + overrides, compute the review surface")
    s.add_argument("project"); s.add_argument("theorems", nargs="*")
    s.add_argument("--spec-module", help="audit every theorem in this module (default <Lib>.Spec)")
    s.add_argument("--no-build", action="store_true", help="skip `lake build`")
    s.add_argument("--paranoid", action="store_true",
                   help="replay through every kernel bundled with Lean (nanoda, con-leche, con-ron, …)")
    s.set_defaults(f=cmd_trust)
    s = sub.add_parser("difftest", help="Lean semantics vs wasmtime on the lifted binaries")
    s.add_argument("project"); s.add_argument("--cases", type=int, default=200); s.add_argument("--seed", type=int, default=0)
    s.set_defaults(f=cmd_difftest)
    s = sub.add_parser("demo", help="end-to-end run on examples/toy + examples/cheat")
    s.add_argument("--cases", type=int, default=200)
    s.set_defaults(f=cmd_demo)
    for sp in sub.choices.values():
        sp.add_argument("--json", action="store_true", help="machine-readable output")
    a = p.parse_args()
    sys.exit(a.f(a))
