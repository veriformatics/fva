"""M8 cheat injection (rubric v1.1): copy a finished project, plant one cheat in the target
theorem (or the shipped wasm), run the arm's own check command, report rc + whether the
output names the problem. Usage: inject.py <project-dir> <lean-file> <theorem> <wasm> <cmd> <out-dir>"""

import re
import shutil
import subprocess
import sys
from pathlib import Path

DECL = re.compile(r"^(@\[|/--|/-!|private |protected |theorem |lemma |def |abbrev |structure |inductive |"
                  r"instance |example |end |namespace |section |open |#|set_option |run_cmd |axiom |noncomputable )")
CHEATS = {
    "C1-sorry": ("", "by sorry"),
    "C2-axiom": ("axiom fvaCheatAx : False\n\n", "fvaCheatAx.elim"),
    "C3-kernel-bypass": ("open Lean Elab Command in\nset_option debug.skipKernelTC true in\n"
                         "run_cmd liftCoreM <| addDecl <| .thmDecl {\n"
                         "  name := `fvaCheatOneEqTwo, levelParams := [],\n"
                         "  type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2),\n"
                         "  value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1) }\n\n",
                         "absurd fvaCheatOneEqTwo (by decide)"),
}


def plant(text: str, thm: str, cheat: str) -> str:
    lines = text.splitlines(keepends=True)
    short = thm.rsplit(".", 1)[-1]
    i = next(k for k, l in enumerate(lines) if re.match(rf"^(private |protected )?(theorem|lemma) {re.escape(short)}\b", l))
    while i > 0 and lines[i - 1].startswith(("@[", "/--")):  # keep attributes/docstring above the prelude
        i -= 1
    t = next(k for k in range(i, len(lines)) if re.match(r"^(private |protected )?(theorem|lemma) ", lines[k]))
    j = next((k for k in range(t + 1, len(lines)) if DECL.match(lines[k])), len(lines))
    block = "".join(lines[i:j])
    head, sep, _ = block.partition(":=")
    if not sep:
        raise SystemExit(f"no := in {thm}")
    pre, proof = CHEATS[cheat]
    new = "".join(lines[:i]) + pre + head + ":= " + proof + "\n\n" + "".join(lines[j:])
    if cheat == "C3-kernel-bypass" and not re.search(r"^import Lean\b", new, re.M):
        new = "import Lean\n" + new
    return new


def flip_code_byte(wasm: Path) -> None:
    b = bytearray(wasm.read_bytes())
    # last code byte before the final `end` (0x0b): an opcode or immediate inside the body
    k = len(b) - 2
    b[k] = (b[k] + 1) % 256
    wasm.write_bytes(bytes(b))


def main() -> None:
    proj, lean_file, thm, wasm, cmd, out = sys.argv[1:7]
    out_dir = Path(out)
    out_dir.mkdir(parents=True, exist_ok=True)
    for cheat in [*CHEATS, "C4-wasm-byte"]:
        work = out_dir / cheat
        if work.exists():
            shutil.rmtree(work)
        shutil.copytree(proj, work, symlinks=True)
        if cheat == "C4-wasm-byte":
            flip_code_byte(work / wasm)
        else:
            f = work / lean_file
            f.write_text(plant(f.read_text(), thm, cheat))
        r = subprocess.run(["bash", "-c", cmd], cwd=work, capture_output=True, text=True, timeout=1800)
        log = r.stdout + r.stderr
        (out_dir / f"{cheat}.log").write_text(log)
        named = bool(re.search(r"sorry|fvaCheat|skipKernelTC|axiom|kernel|reject|mismatch|differ|FAIL|error",
                               log, re.I))
        print(f"{cheat}\trc={r.returncode}\tnames_problem={named}")
        shutil.rmtree(work)


if __name__ == "__main__":
    main()
