"""`fva explain`: the spec in plain English for a reader who cannot read Lean — claimcheck-style
round trip (https://github.com/metareflection/claimcheck): pass 1 explains each claim from the
spec text with comments stripped (so it never sees the author's stated intent), pass 2 compares
that explanation with the intent (docstring, else name). Examples = inputs pass 1 proposes,
outputs computed by Lean from the spec + by wasmtime from the real binary. Advisory: the
verdict stays with `fva trust`."""

import hashlib
import json
import re
import subprocess
import tempfile
import textwrap
from datetime import datetime, timezone
from pathlib import Path

import wasmtime

from . import llm
from . import trust as tr
from .difftest import BITS, _signed
from .lift import decode
from .project import FVA_LEAN, FVA_ROOT, Project

SAVED = "fva-explain.json"
CASE_TIMEOUT = 10  # s; a too-costly case (deep recursion) aborts Lean only after ~25 s
MAX_EXAMPLES = 8
FIXED_INPUTS = [0, 1]  # every claim gets these per argument, whatever the model proposes

EXPLAIN_SCHEMA = {
    "type": "object", "additionalProperties": False, "required": ["claims"],
    "properties": {"claims": {"type": "array", "items": {
        "type": "object", "additionalProperties": False,
        "required": ["name", "summary", "details", "caveats", "examples"],
        "properties": {
            "name": {"type": "string"},
            "summary": {"type": "string"},
            "details": {"type": "array", "items": {"type": "string"}},
            "caveats": {"type": "array", "items": {"type": "string"}},
            "examples": {"type": "array", "items": {"type": "array", "items": {"type": "integer"}}}}}}}}

COMPARE_SCHEMA = {
    "type": "object", "additionalProperties": False, "required": ["claims"],
    "properties": {"claims": {"type": "array", "items": {
        "type": "object", "additionalProperties": False, "required": ["name", "reason", "verdict"],
        "properties": {  # reason before verdict: the reply is generated in this order
            "name": {"type": "string"},
            "reason": {"type": "string"},
            "verdict": {"enum": ["matches", "weaker", "stronger", "different", "vacuous"]}}}}}}

EXPLAIN_PROMPT = """\
You explain a formal specification to a reader who cannot read Lean 4. The specification makes
claims about functions exported by a compiled WebAssembly binary. `Returns m "f" args res` means:
calling exported function f of module m with args terminates without a trap and returns res
(definition below). Lean core names (BitVec, Nat.gcd, …) have their standard Lean 4 meaning.

For each claim in the list, return:
- summary: one sentence in plain English, no Lean notation, that states what the claim guarantees.
- details: short sentences. Name the inputs the claim covers, bit widths, whether a value is read
  as signed or unsigned, wraparound, and what `Returns` adds (termination, no trap).
- caveats: what a reader could misread, what the claim leaves out, or why it may be weaker than
  it looks (vacuous, too narrow, trivially true). Empty when there is nothing.
  Keep example values out of summary, details and caveats; they go in examples alone.
- examples (required for every claim that calls an exported function): 3 to 6 argument lists
  (inputs only, no outputs) that show the behavior, boundary cases included. Integers; negative values are allowed where the claim reads a value as
  signed. Keep values small where the result needs a loop or recursion over the input.

The elaborated statement of each claim = what Lean checks, after every macro and notation the
specification imports has run. It is the truth: where it differs from the source text, explain
the elaborated statement and name the difference in caveats.

=== Elaborated claims ===
{statements}

=== Specification source (comments removed) ===
{spec}

=== FVA WebAssembly semantics (trusted definitions the claims use) ===
{semantics}
"""

COMPARE_PROMPT = """\
Check whether formal claims mean what their authors intended. For each claim you get the
author's stated intent, the formal statement as Lean elaborates it, and an independent
plain-English explanation of that statement, written without seeing the intent, plus
input → output examples that Lean computed from the statement. The formal statement decides:
where the explanation misreads it, follow the statement (for example, a premise that can never
hold makes the claim vacuous). Compare the guarantee, not the wording. Every `Returns` claim
includes termination without a trap; that alone never makes a claim stronger than its intent.
Verdict:
- matches: the claim guarantees what the intent says.
- weaker: the claim guarantees less (narrower inputs, missing cases, a looser result).
- stronger: the claim guarantees more than the intent says.
- different: the claim guarantees something else.
- vacuous: the claim is trivially true or says nothing about the function.
reason: one or two plain-English sentences a non-expert can follow; cite an example if one shows
the gap.

{items}
"""


def strip_comments(text: str) -> str:
    """Drop `/- … -/` blocks (nested; docstrings included) + `--` line comments."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            i = text.find("\n", i) if "\n" in text[i:] else len(text)
        else:
            out.append(text[i])
            i += 1
    return re.sub(r"\n\s*\n+", "\n\n", "".join(out)).strip() + "\n"


def _lean_file(project: Project, body: list[str]) -> str:
    return "\n".join([f"import {project.lib}.Spec", "import FVA.Explain", *body]) + "\n"


def _run_lean(project: Project, source: str, timeout: float) -> tuple[list[dict], bool]:
    """Run `source` (writing JSON lines to `$OUT`); returns the lines + whether Lean finished."""
    with tempfile.TemporaryDirectory() as d:
        out = Path(d) / "out.jsonl"
        out.touch()
        src = project.root / f"FvaExplain_{Path(d).name}.lean"
        src.write_text(source.replace("$OUT", str(out)))
        try:
            r = subprocess.run(["lake", "env", "lean", str(src)], cwd=project.root, timeout=timeout,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            done = r.returncode == 0
        except subprocess.TimeoutExpired:
            done = False
        finally:
            src.unlink()
        return [json.loads(l) for l in out.read_text().splitlines()], done


def _shapes(project: Project, claims: list[str]) -> dict[str, dict]:
    names = ", ".join(f"`{c}" for c in claims)
    rows, done = _run_lean(project, _lean_file(project, [f'#eval FVA.Explain.shapes [{names}] "$OUT"']), 120)
    if not done:
        raise SystemExit("fva explain: reading claim shapes failed")
    return {r["claim"]: r for r in rows}


def _spec_values(project: Project, claim: str, cases: list[list[int]]) -> list[list[int] | None]:
    """Spec-side result per case; `None` = too costly to compute (killed or crashed)."""
    vals: list[list[int] | None] = []
    while len(vals) < len(cases):
        rest = cases[len(vals):]
        lit = "[" + ", ".join("[" + ", ".join(map(str, c)) + "]" for c in rest) + "]"
        rows, _ = _run_lean(project, _lean_file(project, [f'#eval FVA.Explain.run `{claim} {lit} "$OUT"']),
                            CASE_TIMEOUT + 5 * len(rest))
        vals += [[v["value"] for v in r["res"]] for r in rows]
        if len(vals) < len(cases):
            vals.append(None)
    return vals


def _binary_values(wasm: Path, fn: str, cases: list[list[int]]) -> tuple[list[int], list[list[int] | str]]:
    """Result bit widths of `fn` + its results per case from the real binary (`"trap"` on a trap)."""
    data = wasm.read_bytes()
    sig = next(f for f in decode(data) if f.name == fn)
    store = wasmtime.Store()
    f = wasmtime.Instance(store, wasmtime.Module(store.engine, data), []).exports(store)[fn]
    assert isinstance(f, wasmtime.Func)
    rbits = [BITS[t] for t in sig.result_types]
    out: list[list[int] | str] = []
    for c in cases:
        try:
            r = f(store, *[_signed(a, BITS[t]) for a, t in zip(c, sig.params)])
            rs = [] if r is None else r if isinstance(r, list) else [r]
            out.append([v % (1 << b) for v, b in zip(rs, rbits)])
        except wasmtime.Trap:
            out.append("trap")
    return rbits, out


def _mentions(text: str, names: set[str]) -> bool:
    return any(re.search(rf"(?<![\w.]){re.escape(n)}(?![\w.])", text) for n in names)


def _proof_status(t: dict, c: dict) -> dict:
    """Issues of `fva trust` that name this claim or its proofs, + project-wide ones (link,
    syntax, replay, …) that name no claim at all."""
    every = {x["name"] for x in t["claims"]} | {p["name"] for x in t["claims"] for p in x["proofs"]}
    own = {c["name"]} | {p["name"] for p in c["proofs"]}
    mine = [i["detail"] for i in t["issues"] if _mentions(i["detail"], own)]
    shared = sorted({i["kind"] for i in t["issues"] if not _mentions(i["detail"], every)})
    return {"ok": not mine and not shared, "issues": mine, "projectIssues": shared}


def _inputs_sha(project: Project, t: dict, model: str, effort: str) -> str:
    """Everything the LLM text + examples derive from: spec files, binaries, semantics, prompts."""
    h = hashlib.sha256(json.dumps([model, effort, EXPLAIN_PROMPT, COMPARE_PROMPT, EXPLAIN_SCHEMA,
                                   COMPARE_SCHEMA, FIXED_INPUTS, MAX_EXAMPLES]).encode())
    files = sorted({*(s["file"] for s in t["reviewSurface"]), *(l["wasm"] for l in t["implementation"])})
    for rel in files:
        p = project.root / rel if (project.root / rel).exists() else FVA_ROOT / rel
        h.update(rel.encode() + b"\0" + p.read_bytes())
    for p in (FVA_LEAN / "FVA/Wasm/Semantics.lean", FVA_LEAN / "FVA/Explain.lean"):
        h.update(p.read_bytes())
    return h.hexdigest()


def explain(project: Project, model: str = llm.MODEL, effort: str = "medium", force: bool = False) -> dict:
    """Saved explanation (`SAVED` in the project) reused unless `force`: LLM output varies run to
    run, so a reader rereads one fixed text. Proof status = fresh `fva trust` on every call."""
    t = tr.trust(project, [], None)
    base = {"project": str(project.root), "model": model, "trustVerdict": t["verdict"], "trustIssues": t["issues"]}
    if "claims" not in t:
        return base | {"claims": []}
    path = project.root / SAVED
    sha = _inputs_sha(project, t, model, effort)
    if path.exists() and not force:
        saved = json.loads(path.read_text())
        by_name = {c["name"]: c for c in t["claims"]}
        rows = [r | {"proof": _proof_status(t, by_name[r["name"]]) if r["name"] in by_name else
                     {"ok": False, "issues": [f"{r['name']} is no longer in the spec"], "projectIssues": []}}
                for r in saved["claims"]]
        stale = saved["inputsSha"] != sha or set(by_name) != {r["name"] for r in rows}
        return base | {"model": saved["model"], "claims": rows,
                       "saved": {"file": SAVED, "generated": saved["generated"], "reused": True, "stale": stale}}
    rows = _generate(project, t, model, effort)
    rec = {"inputsSha": sha, "generated": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
           "model": model, "effort": effort, "claims": [{k: v for k, v in r.items() if k != "proof"} for r in rows]}
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(rec, indent=1, ensure_ascii=False) + "\n")
    tmp.replace(path)
    return base | {"claims": rows,
                   "saved": {"file": SAVED, "generated": rec["generated"], "reused": False, "stale": False}}


def _generate(project: Project, t: dict, model: str, effort: str) -> list[dict]:
    r = subprocess.run(["lake", "build", "FVA.Explain"], cwd=FVA_LEAN, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"fva explain: building FVA.Explain failed:\n{r.stdout[-2000:]}")
    names = [c["name"] for c in t["claims"]]
    shapes = _shapes(project, names)
    spec = "\n".join(f"--- {s['file']}\n{strip_comments((project.root / s['file']).read_text())}"
                     for s in t["reviewSurface"])
    sem = (FVA_LEAN / "FVA/Wasm/Semantics.lean").read_text()
    prompt = EXPLAIN_PROMPT.format(
        statements="\n".join(f"{n} : Prop := {shapes[n]['statement']}" for n in names if n in shapes),
        spec=spec, semantics=sem)
    p1 = {c["name"]: c for c in llm.ask(prompt, EXPLAIN_SCHEMA, model, effort)["claims"]}
    wasm = {l["module"]: project.root / l["wasm"] for l in t["implementation"]}
    rows = []
    for c in sorted(t["claims"], key=lambda c: c["start"] or 0):
        n, sh = c["name"], shapes.get(c["name"], {}).get("shape")
        e = p1.get(n) or p1.get(n.rsplit(".", 1)[-1]) or {"summary": "", "details": [], "caveats": [], "examples": []}
        row = {"name": n, "intent": shapes.get(n, {}).get("doc") or None, "proof": _proof_status(t, c),
               "statement": shapes.get(n, {}).get("statement"), "summary": e["summary"],
               "details": e["details"], "caveats": e["caveats"], "examples": []}
        if sh and len(c["subjects"]) == 1:
            bits = [p["bits"] for p in sh["params"]]
            fixed = [[v] * len(bits) for v in FIXED_INPUTS]
            cases = [[a % (1 << b) for a, b in zip(x, bits)]
                     for x in [*e["examples"], *fixed] if len(x) == len(bits)]
            cases = list(dict.fromkeys(map(tuple, cases)))[:MAX_EXAMPLES]
            cases = [list(x) for x in cases]
            spec_v = _spec_values(project, n, cases)
            rbits, bin_v = _binary_values(wasm[c["subjects"][0]], sh["fn"], cases)
            row |= {"fn": sh["fn"], "params": sh["params"], "resultBits": rbits,
                    "examples": [{"args": a, "spec": s, "binary": b} for a, s, b in zip(cases, spec_v, bin_v)]}
        rows.append(row)
    items = "\n\n".join(
        f"## {r['name']}\nIntent: {r['intent'] or 'none written; infer it from the name ' + r['name']}\n"
        f"Formal statement: {r['statement']}\n"
        f"Explanation: {r['summary']} {' '.join(r['details'])}\n"
        + "".join(f"Example: {r['fn']}({', '.join(map(str, x['args']))}) → spec says {x['spec']}\n"
                  for x in r["examples"] if x["spec"] is not None)
        for r in rows)
    p2 = {c["name"]: c for c in llm.ask(COMPARE_PROMPT.format(items=items), COMPARE_SCHEMA, model, effort)["claims"]}
    for r in rows:
        v = p2.get(r["name"]) or p2.get(r["name"].rsplit(".", 1)[-1]) or {"verdict": "unknown", "reason": "no reply"}
        r |= {"verdict": v["verdict"], "reason": v["reason"]}
    return rows


def _wrap(text: str, first: str, rest: str) -> list[str]:
    return textwrap.wrap(text, 96, initial_indent=first, subsequent_indent=rest)


def _num(v: int, bits: int) -> str:
    return f"{v} (= {_signed(v, bits)} signed)" if v >= 1 << (bits - 1) else str(v)


def render(r: dict) -> str:
    out = [f"FVA explain — {r['project']}", "",
           f"  Proof check (fva trust): {r['trustVerdict']}"
           + ("" if r["trustVerdict"] == "PASS" else " — the claims below are not all proven; run `fva trust` for the reasons"),
           f"  The text below was written by {r['model']} and can be wrong. It helps you read the spec;",
           "  it does not replace the proof check. The examples are computed, not written by the model."]
    if sv := r.get("saved"):
        if sv["stale"]:
            out += ["", f"  STALE: the spec, the binary, or the prompts changed after {sv['generated']}.",
                    "  The text below describes the old version. Run again with --force to regenerate it."]
        elif sv["reused"]:
            out += ["", f"  Saved text from {sv['generated']} ({sv['file']}). The proof status is current.",
                    "  Run again with --force to regenerate the text."]
        else:
            out += ["", f"  Saved to {sv['file']}. Later runs show this text; use --force to regenerate it."]
    for c in r["claims"]:
        mark = "✓" if c["verdict"] == "matches" else "✗"
        pr = c["proof"]
        proof = ("✓ Proof: checked by fva trust" if pr["ok"] else "✗ Proof: not accepted — "
                 + "; ".join(pr["issues"] + ([f"project checks failed: {', '.join(pr['projectIssues'])}"]
                                            if pr["projectIssues"] else [])))
        out += ["", c["name"], *_wrap(proof, "  ", "    "), *_wrap(c["summary"], "  In plain English: ", "    ")]
        out += [l for d in c["details"] for l in _wrap(d, "    - ", "      ")]
        if c["caveats"]:
            out.append("  Watch for:")
            out += [l for d in c["caveats"] for l in _wrap(d, "    - ", "      ")]
        if c["examples"]:
            width = [p["bits"] for p in c["params"]]
            out.append("  Examples (spec value computed by Lean; binary value from wasmtime):")
            for x in c["examples"]:
                call = f"{c['fn']}({', '.join(_num(a, b) for a, b in zip(x['args'], width))})"
                s = "too costly to compute" if x["spec"] is None else ", ".join(_num(v, b) for v, b in zip(x["spec"], c["resultBits"]))
                agree = "" if x["spec"] is None else ("  binary agrees" if x["binary"] == x["spec"]
                                                      else f"  ✗ binary returns {x['binary']}")
                out += _wrap(f"{call} → {s}{agree}", "    ", "        ")
        elif c["statement"] and not c.get("fn"):
            out += ["  Examples: none. FVA computes examples only for claims of the form",
                    "  `∀ inputs, Returns …`. Lean reads this claim as:",
                    *_wrap(" ".join(c["statement"].split()), "    ", "      ")]
        intent = c["intent"] or f"(no description; inferred from the name {c['name'].rsplit('.', 1)[-1]})"
        out += [*_wrap(intent, "  Stated intent: ", "    "),
                *_wrap(f"{c['verdict'].upper()} — {c['reason']}", f"  {mark} Intent check: ", "    ")]
    return "\n".join(out)
