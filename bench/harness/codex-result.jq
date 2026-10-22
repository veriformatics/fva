# Input = JSONL slurped to an array; transport/timeout status stays with the runner.
def count_type($type): [.[] | select(.type == $type)] | length;
def natural: type == "number" and . >= 0 and floor == .;
def optional_natural($key): (has($key) | not) or (.[$key] | natural);
if length == 0 or any(.[]; type != "object" or (.type | type != "string")) then
  error("empty or invalid Codex event stream")
else . end |
[.[] | select(.type == "turn.completed")] as $completed |
if any($completed[]; .usage |
  (([.input_tokens, .cached_input_tokens, .output_tokens] | all(natural)) and
    optional_natural("cache_write_input_tokens") and
    optional_natural("reasoning_output_tokens") | not))
then error("invalid completed-turn usage") else . end |
# Codex 0.163's usage_from_last_total emits thread totals, not per-turn deltas.
($completed[-1].usage // null) as $snapshot |
(count_type("turn.started")) as $started |
(count_type("turn.failed")) as $failed |
(if $failed > 0 or .[-1].type == "error" then "agent_error"
 elif ($completed | length) > 0 and .[-1].type == "turn.completed" then "completed"
 else "incomplete_result" end) as $status |
{
  status: $status,
  thread_id: ([.[] | select(.type == "thread.started") | .thread_id][0] // null),
  turns_started: $started,
  turns_completed: ($completed | length),
  turns_failed: $failed,
  error_events: count_type("error"),
  usage_complete: ($status == "completed"),
  usage: (if ($completed | length) == 0 then null else {
    input_tokens: $snapshot.input_tokens,
    output_tokens: $snapshot.output_tokens,
    cache_read_input_tokens: $snapshot.cached_input_tokens,
    cache_write_input_tokens: ($snapshot.cache_write_input_tokens // null),
    reasoning_output_tokens: ($snapshot.reasoning_output_tokens // null),
    cost_usd: null,
    duration_api_ms: null
  } end)
}
