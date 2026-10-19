"""`fva trust`: verdict + minimal human-review surface for a lake project's spec theorems."""

import hashlib
import json
import re
import subprocess
import tempfile
import time
from pathlib import Path

from .lift import to_lean
from .project import FVA_LEAN, FVA_ROOT, TRUST_BIN, Project, code_lines, ensure_trust_bin

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Core plumbing a reader never needs named: instances, recursors, matchers, literals.
CORE_NOISE = ("inst", "OfNat.ofNat", "HAdd.hAdd", "Nat.below", "Nat.brecOn", "Nat.casesOn", "Nat.succ",
              "Unit", "PProd", "Eq", "Bool", "List.cons", "List.nil", "ite")


def _lift_link(project: Project) -> list[dict]:
    links = []
    for l in project.lifted():
        row = {"module": l.module, "file": str(l.path.relative_to(project.root)),
               "wasm": str(l.wasm.relative_to(project.root)), "pinnedSha": l.sha}
        if not l.wasm.exists():
            row |= {"wasmPresent": False, "shaMatch": False, "reliftIdentical": False}
        else:
            data = l.wasm.read_bytes()
            src = row["wasm"]
            row |= {"wasmPresent": True, "bytes": len(data),
                    "shaMatch": hashlib.sha256(data).hexdigest() == l.sha,
                    "reliftIdentical": to_lean(data, l.ns, src) == l.path.read_text()}
        links.append(row)
    return links


def _ranges_lines(path: Path, ranges: list[tuple[int, int]]) -> tuple[int, int]:
    lines = path.read_text().splitlines()
    picked = sorted({i for a, b in ranges for i in range(a, b + 1)})
    return code_lines([lines[i - 1] for i in picked]), len(picked)


def _replay(project: Project, module: str, theorems: list[str], paranoid: bool) -> dict:
    """Export the theorems + their dependency closure from the built .oleans, then replay the
    export through the kernel(s) via `lake check`. Catches declarations that entered the
    environment without a kernel check (`debug.skipKernelTC`, metaprogrammed `addDecl`)."""
    with tempfile.TemporaryDirectory() as d:
        export = Path(d) / "export.ndjson"
        with export.open("w") as fh:
            e = subprocess.run(["lake", "env", "leanexport", module, "--", *theorems],
                               cwd=project.root, stdout=fh, stderr=subprocess.PIPE, text=True)
        if e.returncode != 0:
            return {"ok": False, "kernels": [], "detail": e.stderr[-800:]}
        t = time.monotonic()
        r = subprocess.run(["lake", "check", f"--from-export={export}", *(["--paranoid"] if paranoid else [])],
                           cwd=project.root, capture_output=True, text=True)
    log = r.stdout + r.stderr
    return {"ok": r.returncode == 0, "seconds": round(time.monotonic() - t, 1),
            "accepted": re.findall(r"^(.+?) kernel accepts", log, re.M),
            "rejected": re.findall(r"^(.+?) kernel rejected", log, re.M),
            "detail": "" if r.returncode == 0 else log[-800:]}


def trust(project: Project, theorems: list[str], spec_module: str | None, build: bool = True,
          paranoid: bool = False) -> dict:
    ensure_trust_bin()
    issues = []
    build_ok, build_s = True, 0.0
    if build:
        build_ok, build_s, log = project.build()
        if not build_ok:
            issues.append({"kind": "build", "detail": log[-1500:]})
    links = _lift_link(project)
    if not links:
        issues.append({"kind": "link", "detail": "no lifted implementation module (fva lift) in project"})
    for l in links:
        if not (l["shaMatch"] and l["reliftIdentical"]):
            issues.append({"kind": "link", "detail": f"{l['file']} ≠ fva lift of {l['wasm']}"
                           f" (sha match: {l['shaMatch']}, re-lift identical: {l['reliftIdentical']})"})
    spec = spec_module or f"{project.lib}.Spec"
    if not build_ok:
        return {"project": str(project.root), "verdict": "FAIL", "issues": issues, "build": {"ok": False, "seconds": round(build_s, 1)}}
    cmd = ["lake", "env", str(TRUST_BIN), "--spec-module", spec, "--base-dir", str(FVA_LEAN / ".lake/build/lib/lean")]
    for l in links:
        cmd += ["--subject", l["module"]]
    r = subprocess.run(cmd, cwd=project.root, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"fva: fva-trust failed (rc={r.returncode}): {r.stderr.strip()}")
    rep = json.loads(r.stdout)

    claims = [c for c in rep["claims"] if not theorems or c["name"] in theorems]
    if not claims:
        issues.append({"kind": "claims", "detail": f"no claims in {spec} (Prop-valued defs or theorems)"})
    for c in claims:
        if not c["proofs"]:
            issues.append({"kind": "unproven", "detail": f"{c['name']} has no theorem proving it"})
        if not c["subjects"]:
            issues.append({"kind": "vacuous", "detail": f"{c['name']} never mentions the implementation"})
        if c["kind"] == "theorem":
            issues.append({"kind": "layout", "detail": f"{c['name']} is proven inside the spec module;"
                           " its proof text joins the review surface"})
        for p in c["proofs"]:
            bad = sorted(set(p["axioms"]) - STANDARD_AXIOMS)
            if bad:
                issues.append({"kind": "axiom", "detail": f"{p['name']} (proof of {c['name']}) depends on {', '.join(bad)}"})
    for f in rep["flags"]:
        issues.append({"kind": "override", "detail": f"{f['name']} ({f['module']}) is {f['issue']}"})
    for m in rep["reviewModules"]:
        if m["syntaxExtensions"]:
            issues.append({"kind": "syntax", "detail": f"{m['module']} extends syntax ({len(m['syntaxExtensions'])} "
                           "macro/notation/elaborator decls); the spec text no longer means what it reads"})
    proofs = [p["name"] for c in claims for p in c["proofs"]]
    replay = _replay(project, project.lib, proofs, paranoid) if proofs else {"ok": False, "accepted": [], "rejected": [], "seconds": 0, "detail": "no proofs"}
    if not replay["ok"]:
        issues.append({"kind": "replay", "detail": "kernel replay of the exported proofs failed: "
                       + (", ".join(replay.get("rejected", [])) or replay["detail"][-300:])})

    # review surface = every review module, read whole (spec text parses under all of it)
    surface = []
    for m in rep["reviewModules"]:
        path = project.module_path(m["module"])
        lines = path.read_text().splitlines()
        surface.append({"file": _rel(project, path), "codeLines": code_lines(lines), "lines": len(lines),
                        "decls": [d.removeprefix(project.lib + ".") for d in m["decls"] if ".match_" not in d]})
    review_files = {s["file"] for s in surface}
    lifted_files = {l["file"] for l in links}
    sem = FVA_LEAN / "FVA/Wasm/Semantics.lean"
    lift_py = FVA_ROOT / "src/fva/lift.py"
    return {
        "project": str(project.root),
        "verdict": "PASS" if not issues else "FAIL",
        "issues": issues,
        "build": {"ok": build_ok, "seconds": round(build_s, 1)} if build else None,
        "kernelReplay": replay,
        "claims": claims,
        "axioms": rep["allAxioms"],
        "implementation": links,
        "reviewSurface": surface,
        "reviewSurfaceCodeLines": sum(s["codeLines"] for s in surface),
        "trustedBase": {
            "axioms": sorted(STANDARD_AXIOMS),
            "semantics": {"file": str(sem.relative_to(FVA_ROOT)), "codeLines": code_lines(sem.read_text().splitlines()),
                          "usedBySpec": rep["baseUsed"]},
            "lifter": {"file": str(lift_py.relative_to(FVA_ROOT)), "codeLines": _py_lines(lift_py)},
            "coreDefinitionsUsed": sorted(n for n in rep["coreUsed"] if not n.startswith(CORE_NOISE)
                                          and not n.rsplit(".", 1)[-1].startswith("inst")),
        },
        "unreviewed": {
            "proofs": [{"file": _rel(project, p), "codeLines": code_lines(p.read_text().splitlines())}
                       for p in project.sources() if _rel(project, p) not in review_files | lifted_files],
            "implementation": [{"file": l["file"], "codeLines": code_lines((project.root / l["file"]).read_text().splitlines()),
                                "from": l["wasm"]} for l in links],
        },
        "auditedConstants": rep["auditClosureSize"],
    }


def _rel(project: Project, p: Path) -> str:
    try:
        return str(p.relative_to(project.root))
    except ValueError:
        return str(p.relative_to(FVA_ROOT))


def _py_lines(p: Path) -> int:
    n, in_doc = 0, False
    for line in p.read_text().splitlines():
        s = line.strip()
        if s.count('"""') % 2:
            in_doc = not in_doc
            continue
        n += bool(s) and not in_doc and not s.startswith(("#", '"""'))
    return n


def _n(k: int) -> str:
    return f"{k} line" + ("" if k == 1 else "s")


def render(r: dict) -> str:
    ok = lambda b: "✓" if b else "✗"
    out = [f"FVA trust report — {r['project']}", "",
           f"  Verdict: {r['verdict']}" + ("" if r["verdict"] == "PASS" else f" ({len(r['issues'])} issue(s))")]
    for i in r["issues"]:
        out.append(f"    ✗ [{i['kind']}] {i['detail']}")
    if "claims" not in r:  # build failed: nothing further was checked
        return "\n".join(out)
    if r["build"]:
        out.append(f"  lake build: {'passed' if r['build']['ok'] else 'FAILED'} ({r['build']['seconds']} s; "
                   "accepts sorry + axioms, so the verdict rests on the audit below)")
    k = r["kernelReplay"]
    out.append(f"  kernel replay of exported proofs: "
               + (f"accepted by {', '.join(k['accepted'])} ({k['seconds']} s)" if k["ok"]
                  else f"REJECTED by {', '.join(k.get('rejected', [])) or 'export step'}"))
    out += ["", "Claims (✓ = proof uses standard axioms + claim mentions the implementation;"
            " link, syntax + replay checks above cover all claims)"]
    for c in r["claims"]:
        prf = c["proofs"]
        good = c["subjects"] and prf and all(set(p["axioms"]) <= STANDARD_AXIOMS for p in prf)
        about = ", ".join(c["subjects"]) or "nothing — does not mention the implementation"
        how = "; ".join(f"proved by {p['name']} (axioms: {', '.join(p['axioms']) or 'none'})" for p in prf) or "UNPROVEN"
        out.append(f"  {ok(good)} {c['name']}  about {about}\n      {how}")
    out += ["", "Implementation link (claims quantify over these exact bytes)"]
    for l in r["implementation"]:
        out.append(f"  {ok(l['shaMatch'] and l['reliftIdentical'])} {l['file']} ← {l['wasm']}"
                   f"  sha256 {l['pinnedSha'][:12]}…  pinned {ok(l['shaMatch'])}  re-lift identical {ok(l['reliftIdentical'])}")
    out += ["", f"Read these: {r['reviewSurfaceCodeLines']} lines of spec (whole files; comments excluded)"]
    for s in r["reviewSurface"]:
        out.append(f"  {s['file']:<24} {s['codeLines']:>3} lines  {', '.join(s['decls'])}")
    tb = r["trustedBase"]
    out += ["", "Trusted once, shared by every FVA project",
            f"  Lean kernel + axioms {', '.join(tb['axioms'])}",
            f"  WASM semantics   {tb['semantics']['file']} ({tb['semantics']['codeLines']} lines;"
            f" spec uses {', '.join(n.removeprefix('FVA.Wasm.') for n in tb['semantics']['usedBySpec'])})",
            f"  wasm → Lean lifter  {tb['lifter']['file']} ({tb['lifter']['codeLines']} lines)",
            f"  Lean core definitions in the spec (instances + plumbing omitted): {', '.join(tb['coreDefinitionsUsed'])}"]
    u = r["unreviewed"]
    out += ["", "Never read (checked by the Lean kernel)"]
    for p in u["proofs"]:
        out.append(f"  proofs + glue   {p['file']} ({_n(p['codeLines'])})")
    for i in u["implementation"]:
        out.append(f"  implementation  {i['file']} ({_n(i['codeLines'])}, lifted from {i['from']}; "
                   "source code + compiler untrusted)")
    out.append(f"  audit: {r['auditedConstants']} non-core constants scanned for "
               "implemented_by / extern / unsafe / partial / opaque")
    return "\n".join(out)
