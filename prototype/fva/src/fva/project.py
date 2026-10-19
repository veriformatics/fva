"""Lake project helpers shared by the CLI commands."""

import re
import subprocess
import time
import tomllib
from dataclasses import dataclass
from pathlib import Path

FVA_ROOT = Path(__file__).resolve().parents[2]
FVA_LEAN = FVA_ROOT / "lean"
TRUST_BIN = FVA_LEAN / ".lake/build/bin/fva-trust"
LIFTED_RE = re.compile(r'from `(?P<src>[^`]+)`.*?def wasmSha256 : String := "(?P<sha>[0-9a-f]{64})"', re.S)
NS_RE = re.compile(r"^namespace (\S+)", re.M)


@dataclass
class Lifted:
    module: str
    path: Path
    wasm: Path
    sha: str
    ns: str


class Project:
    def __init__(self, root: Path):
        self.root = root.resolve()
        cfg = tomllib.loads((self.root / "lakefile.toml").read_text())
        self.lib = cfg["lean_lib"][0]["name"]

    def module_path(self, module: str) -> Path | None:
        rel = Path(*module.split(".")).with_suffix(".lean")
        for base in (self.root, FVA_LEAN):
            if (base / rel).exists():
                return base / rel
        return None

    def module_of(self, path: Path) -> str:
        return ".".join(path.relative_to(self.root).with_suffix("").parts)

    def sources(self) -> list[Path]:
        return sorted(p for p in self.root.rglob("*.lean")
                      if ".lake" not in p.parts and p.name != "lakefile.lean")

    def lifted(self) -> list[Lifted]:
        out = []
        for p in self.sources():
            text = p.read_text()
            if (m := LIFTED_RE.search(text)) and (ns := NS_RE.search(text)):
                out.append(Lifted(self.module_of(p), p, self.root / m["src"], m["sha"], ns[1]))
        return out

    def run(self, *cmd: str, check: bool = True) -> subprocess.CompletedProcess:
        return subprocess.run(cmd, cwd=self.root, capture_output=True, text=True, check=check)

    def build(self) -> tuple[bool, float, str]:
        t = time.monotonic()
        r = self.run("lake", "build", check=False)
        log = "\n".join(l for l in (r.stdout + r.stderr).splitlines() if not l.startswith("trace"))
        return r.returncode == 0, time.monotonic() - t, log


def ensure_trust_bin() -> None:
    r = subprocess.run(["lake", "build", "fva-trust"], cwd=FVA_LEAN, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"fva: building fva-trust failed:\n{r.stdout[-2000:]}")


def code_lines(lines: list[str]) -> int:
    """Lines carrying Lean code: blank lines, `--` comments + `/- … -/` blocks (docstrings) excluded."""
    n, depth = 0, 0
    for line in lines:
        s, code = line, False
        while s:
            if depth:
                i, j = s.find("/-"), s.find("-/")
                if j < 0 and i < 0:
                    break
                if 0 <= i < j or j < 0:
                    depth, s = depth + 1, s[i + 2:]
                else:
                    depth, s = depth - 1, s[j + 2:]
                continue
            st = s.lstrip()
            if not st or st.startswith("--"):
                break
            i = s.find("/-")
            if i < 0:
                code = True
                break
            if s[:i].strip():
                code = True
            depth, s = 1, s[i + 2:]
        n += code
    return n
