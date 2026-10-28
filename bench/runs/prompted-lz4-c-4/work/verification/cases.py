"""Concrete test vectors, not a formalization of the LZ4 language."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def extension(n):
    return [255] * (n // 255) + [n % 255]


def literals(data, low=0):
    n = len(data)
    return [16 * min(n, 15) + low] + (extension(n - 15) if n >= 15 else []) + data


def cases():
    result = []

    def add(name, data, cap, ret, output=None, src=131072, dst=1048576):
        assert 131072 <= src < 2097152 and src + len(data) <= 2097152
        assert 131072 < dst and dst + cap < 2097152  # leave guard bytes
        assert src + len(data) <= dst - 1 or dst + cap + 1 <= src
        assert ret < 0 or (output is not None and len(output) == ret <= cap)
        result.append(dict(name=name, data=data, cap=cap, ret=max(ret, -1), output=output,
                           src=src, dst=dst))

    for cap in [0, 1, 32]:
        add(f"no-input/{cap}", [], cap, -1)
        for b in range(256):
            r = (0 if b == 0 else -1) if cap == 0 else (0 if b < 16 else -2)
            add(f"single-byte/{b}/{cap}", [b], cap, r, [] if r == 0 else None)
    for n in list(range(15)) + [15, 16, 254, 255, 269, 270, 271, 525]:
        data = [(37 * i + 11) % 256 for i in range(n)]
        encoded = literals(data)
        for cap in [max(1, n), n + 64]:
            add(f"literal/{n}/{cap}", encoded, cap, n, data)
        if n:
            add(f"literal-small-cap/{n}", encoded, n - 1, -1 if n == 1 else -2)
    for offset in [1, 2, 3, 4, 7, 8, 9, 16]:
        prefix = [(31 * i + 17) % 256 for i in range(offset)]
        for length in [7, 8, 15, 18, 19, 20, 255, 274]:
            encoded = literals(prefix, min(length - 4, 15)) + [offset, 0]
            if length >= 19:
                encoded += extension(length - 19)
            tail = [23, 45, 67, 89, 101]
            encoded += literals(tail)
            output = prefix[:]
            for _ in range(length):
                output.append(output[-offset])
            output += tail
            for extra in [0, 64]:
                add(f"match/{offset}/{length}/{extra}", encoded, len(output) + extra,
                    len(output), output)
    for length in [7, 8, 18, 19, 64]:
        encoded = [min(length - 4, 15), 0, 0]
        if length >= 19:
            encoded += extension(length - 19)
        output = [0] * length + [1, 2, 3, 4, 5]
        encoded += literals([1, 2, 3, 4, 5])
        add(f"zero-offset/{length}", encoded, len(output) + 64, len(output), output)
    for name, data in [("bad-offset", [0x10, 65, 2, 0, 0x50, 1, 2, 3, 4, 5]),
                       ("truncated-literal", [0x20, 65]),
                       ("truncated-extension", [0xF0, 255])]:
        add(name, data, 128, -2 if name != "bad-offset" else -5)
    # Repeat useful cases with reversed, adjacent, and near-memory-end buffers.
    for original in result[771:]:
        if original["ret"] < 0:
            continue
        for src, dst in [(1048576, 131073), (131072, 131073 + len(original["data"])),
                         (131072, 2097150 - original["cap"])]:
            add(original["name"] + f"/layout/{dst}", original["data"], original["cap"],
                original["ret"], original["output"], src, dst)
    return result


def wast(tests, false=False):
    blob = (ROOT / "lz4-c.wasm").read_bytes()
    escaped = "".join(f"\\{b:02x}" for b in blob)
    out = [f'(module $artifact binary "{escaped}")', '(register "artifact" $artifact)',
           '''(module $h
             (import "artifact" "memory" (memory 32 32))
             (import "artifact" "LZ4_decompress_safe"
               (func $decode (param i32 i32 i32 i32) (result i32)))
             (func (export "poke") (param i32 i32)
               local.get 0 local.get 1 i32.store8)
             (func (export "peek") (param i32) (result i32)
               local.get 0 i32.load8_u)
             (func (export "fill") (param i32 i32)
               local.get 0 i32.const 165 local.get 1 memory.fill)
             (func (export "go") (param i32 i32 i32 i32) (result i32) (local i32)
               local.get 0 local.get 1 local.get 2 local.get 3 call $decode
               local.tee 4 i32.const 0 i32.lt_s
               if (result i32) i32.const -1 else local.get 4 end))''']
    if false:
        tests = tests[:1]
    for t in tests:
        s, d, c = t["src"], t["dst"], t["cap"]
        out.append(f'(invoke $h "fill" (i32.const {d - 1}) (i32.const {c + 2}))')
        for i, b in enumerate(t["data"]):
            out.append(f'(invoke $h "poke" (i32.const {s + i}) (i32.const {b}))')
        expected = t["ret"] + (1 if false else 0)
        out.append(f'(assert_return (invoke $h "go" (i32.const {s}) (i32.const {d}) '
                   f'(i32.const {len(t["data"])}) (i32.const {c})) (i32.const {expected}))')
        for a, b in ([(d - 1, 165), (d + c, 165)] +
                     [(s + i, b) for i, b in enumerate(t["data"])] +
                     [(d + i, b) for i, b in enumerate(t["output"] or [])]):
            out.append(f'(assert_return (invoke $h "peek" (i32.const {a})) (i32.const {b}))')
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    tests = cases()
    (ROOT / "verification/cases.json").write_text(json.dumps(tests))
    (ROOT / "verification/cases.wast").write_text(wast(tests))
    (ROOT / "verification/false.wast").write_text(wast(tests, false=True))
    print(f"Generated {len(tests)} concrete executions")
