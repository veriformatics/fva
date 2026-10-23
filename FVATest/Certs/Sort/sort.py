import sys

xs = [int(line) for line in sys.stdin if line.strip()]
sys.stdout.write("".join(f"{x}\n" for x in sorted(xs)))
