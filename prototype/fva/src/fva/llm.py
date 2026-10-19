"""Structured LLM calls through `codex app-server` (JSON-RPC over stdio): one ephemeral,
read-only thread per call, reply constrained by a JSON schema."""

import json
import subprocess
import threading
import time

MODEL = "gpt-6-luna"


class LLMError(Exception):
    pass


def ask(prompt: str, schema: dict, model: str = MODEL, effort: str = "medium", timeout: float = 600) -> dict:
    p = subprocess.Popen(["codex", "app-server"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.DEVNULL, text=True, bufsize=1)
    assert p.stdin and p.stdout
    inp, out = p.stdin, p.stdout
    ids = iter(range(1, 1 << 30))

    def send(method: str, params: dict | None = None, notify: bool = False) -> int:
        msg = {"method": method, "params": params or {}}
        if not notify:
            msg["id"] = next(ids)
        inp.write(json.dumps(msg) + "\n")
        return msg.get("id", 0)

    def until(pred) -> dict:
        while time.monotonic() < deadline:
            line = out.readline()
            if not line:
                raise LLMError("codex app-server exited")
            m = json.loads(line)
            if "id" in m and "method" in m:  # server → client request (approval etc.): refuse
                inp.write(json.dumps({"id": m["id"], "error": {"code": -32601, "message": "unsupported"}}) + "\n")
                continue
            if "error" in m and "method" not in m:
                raise LLMError(json.dumps(m["error"])[:500])
            if pred(m):
                return m
        raise LLMError(f"no reply within {timeout:.0f} s")

    deadline = time.monotonic() + timeout
    killer = threading.Timer(timeout, p.kill)  # readline blocks past `deadline` on a silent server
    killer.start()
    try:
        i = send("initialize", {"clientInfo": {"name": "fva", "version": "0"}})
        until(lambda m: m.get("id") == i)
        send("initialized", notify=True)
        i = send("thread/start", {"model": model, "ephemeral": True, "sandbox": "read-only",
                                  "approvalPolicy": "never", "cwd": "/tmp",
                                  "developerInstructions": "Answer from the text in the prompt alone. "
                                                           "Run no commands and read no files."})
        thread = until(lambda m: m.get("id") == i)["result"]["thread"]["id"]
        send("turn/start", {"threadId": thread, "input": [{"type": "text", "text": prompt}],
                            "outputSchema": schema, "effort": effort})
        text = ""
        while True:
            m = until(lambda m: m.get("method") in ("item/completed", "turn/completed", "error"))
            if m["method"] == "error":
                raise LLMError(json.dumps(m["params"])[:500])
            if m["method"] == "item/completed" and m["params"]["item"].get("type") == "agentMessage":
                text = m["params"]["item"].get("text", "")
            if m["method"] == "turn/completed":
                break
        try:
            return json.loads(text)
        except json.JSONDecodeError as e:
            raise LLMError(f"reply is not JSON: {text[:300]!r}") from e
    finally:
        killer.cancel()
        p.kill()
        p.wait()
