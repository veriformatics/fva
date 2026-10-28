import Lean.Data.Json

/-!
# Structured LLM calls through `codex app-server`

JSON-RPC over stdio: one ephemeral, read-only thread per call, the reply constrained by a JSON
schema. Server-to-client requests (approvals) are refused. A timer task kills a silent server,
since a blocked `getLine` never sees the deadline.
-/

namespace FVA.Tool.Codex

open Lean

/-- The model `fva explain` asks unless told otherwise (Decisions: LLM backend). -/
def defaultModel : String := "gpt-6-luna"

/-- `codex app-server` arguments: no shell, image viewer or MCP tool. A read-only sandbox still
lets the model read any local file, and project text (identifiers, literals, claim docstrings)
reaches the prompt, so an injected request could copy a file into the saved explanation. An
unknown feature name stops the server: a codex that renames one fails closed. -/
def serverArgs : Array String :=
  #["app-server", "--disable", "shell_tool", "--disable", "unified_exec", "--disable",
    "view_image", "-c", "mcp_servers={}"]

/-- One JSON-RPC session with a running `codex app-server`. -/
structure Session where
  /-- Writes requests. -/
  out : IO.FS.Handle
  /-- Reads replies and notifications. -/
  inp : IO.FS.Handle
  /-- The next request id. -/
  next : IO.Ref Nat

/-- Send a request (a fresh id, returned) or, with `notify`, a notification. -/
def Session.send (s : Session) (method : String) (params : Json) (notify := false) : IO Nat := do
  let id ← s.next.modifyGet fun n => (n, n + 1)
  let base := [("method", toJson method), ("params", params)]
  s.out.putStrLn (Json.mkObj (if notify then base else ("id", toJson id) :: base)).compress
  s.out.flush
  return id

/-- Read messages until one satisfies `pred`; refuse server requests, fail on an error reply. -/
partial def Session.until (s : Session) (pred : Json → Bool) : IO Json := do
  let line ← s.inp.getLine
  if line.isEmpty then throw <| .userError "codex app-server exited (or timed out)"
  let m ← IO.ofExcept (Json.parse line)
  let id := (m.getObjVal? "id").toOption
  let method := (m.getObjValAs? String "method").toOption
  if let (some i, some _) := (id, method) then
    s.out.putStrLn (Json.mkObj [("id", i), ("error", Json.mkObj
      [("code", toJson (-32601 : Int)), ("message", "unsupported")])]).compress
    s.out.flush
    s.until pred
  else if method.isNone && (m.getObjVal? "error").isOk then
    throw <| .userError s!"codex app-server error: {(m.getObjValD "error").compress.take 500}"
  else if pred m then return m
  else s.until pred

/-- Ask `prompt` in a fresh thread; the reply text, constrained by `schema`, parsed as JSON. -/
def ask (prompt : String) (schema : Json) (model effort : String) (timeoutMs : Nat := 600000) :
    IO Json := do
  let child ← IO.Process.spawn
    { cmd := "codex", args := serverArgs, stdin := .piped, stdout := .piped,
      stderr := .null }
  -- polls in steps: the process exits only once this task ends, so a cancel must end it soon
  let killer ← IO.asTask (prio := .dedicated) do
    let deadline := (← IO.monoMsNow) + timeoutMs
    while (← IO.monoMsNow) < deadline do
      if ← IO.checkCanceled then return
      IO.sleep 100
    child.kill
  let next ← IO.mkRef 1
  let s : Session := { out := child.stdin, inp := child.stdout, next }
  try
    let isReply (i : Nat) (m : Json) := (m.getObjValAs? Nat "id").toOption == some i
    let i ← s.send "initialize" (Json.mkObj [("clientInfo",
      Json.mkObj [("name", "fva"), ("version", "0")])])
    let _ ← s.until (isReply i)
    let _ ← s.send "initialized" (Json.mkObj []) (notify := true)
    let i ← s.send "thread/start" (Json.mkObj [("model", toJson model), ("ephemeral", true),
      ("sandbox", "read-only"), ("approvalPolicy", "never"), ("cwd", "/tmp"),
      ("developerInstructions",
        "Answer from the text in the prompt alone. Run no commands and read no files.")])
    let r ← s.until (isReply i)
    let thread ← IO.ofExcept <|
      ((r.getObjValD "result").getObjValD "thread").getObjValAs? String "id"
    let _ ← s.send "turn/start" (Json.mkObj [("threadId", toJson thread),
      ("input", Json.arr #[Json.mkObj [("type", "text"), ("text", toJson prompt)]]),
      ("outputSchema", schema), ("effort", toJson effort)])
    let mut text := ""
    repeat
      let m ← s.until fun m => ["item/completed", "turn/completed", "error"].contains
        ((m.getObjValAs? String "method").toOption.getD "")
      let method := (m.getObjValAs? String "method").toOption.getD ""
      if method == "error" then
        throw <| .userError s!"codex: {(m.getObjValD "params").compress.take 500}"
      let item := (m.getObjValD "params").getObjValD "item"
      if method == "item/completed" &&
          (item.getObjValAs? String "type").toOption == some "agentMessage" then
        text := (item.getObjValAs? String "text").toOption.getD ""
      if method == "turn/completed" then break
    match Json.parse text with
    | .ok j => return j
    | .error _ => throw <| .userError s!"codex: the reply is not JSON: {text.take 300}"
  finally
    IO.cancel killer
    try child.kill catch _ => pure ()
    let _ ← child.wait

end FVA.Tool.Codex
