#!/usr/bin/env python3
"""Render explicit fixtures as Lean data; --check is read-only."""
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent


def render():
    cases = json.loads((ROOT / "verification/cases.json").read_text())
    lines = ["-- Generated from verification/cases.json by verification/gen_cases.py.",
             "import Proofs.Checks", "namespace Verification", "",
             "def cases : List Case := ["]
    for i, c in enumerate(cases):
        lines += ["  {", f'    name := {json.dumps(c["name"])}',
                  f'    input := {c["input"]}', f'    cap := {c["cap"]}',
                  f'    result := {c["result"] % (1 << 32)}',
                  f'    output := {c["output"]}', "    sequences := ["]
        for j, s in enumerate(c["sequences"]):
            fields = ", ".join(f"{k} := {v}" for k, v in s.items())
            lines += ["      { " + fields + " }" +
                      ("," if j + 1 < len(c["sequences"]) else "")]
        lines += ["    ]", f'    validEnd := {str(c["validEnd"]).lower()}',
                  f'    src := {c.get("src", 131072)}',
                  f'    dst := {c.get("dst", 262144)}',
                  "  }" + ("," if i + 1 < len(cases) else "")]
    lines += ["]", "", "end Verification", ""]
    return "\n".join(lines)


if __name__ == "__main__":
    text = render()
    target = ROOT / "Proofs/Cases.lean"
    if sys.argv[1:] == ["--check"]:
        assert target.read_text() == text
        print("PASS: generated Lean fixtures match cases.json")
    else:
        assert not sys.argv[1:]
        target.write_text(text)
        print("wrote Proofs/Cases.lean")
