"""Fresh local proof build and supplementary runtime replays. No network needed."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
commands = [
    ['sha256sum', '-c', 'verification/inputs.sha256'],
    ['python3', 'verification/generate.py', '--check'],
    ['lake', 'clean', 'proofs'],
    ['lake', 'build'],
    ['Rscript', 'verification/replay_edger.R'],
    ['python3', 'verification/replay_rnanorm.py'],
]
for command in commands:
    print('+ ' + ' '.join(command), flush=True)
    subprocess.run(command, cwd=root, check=True)
print('ALL VERIFICATION CHECKS PASSED (R3 is refuted; see VERIFICATION.md).', flush=True)
