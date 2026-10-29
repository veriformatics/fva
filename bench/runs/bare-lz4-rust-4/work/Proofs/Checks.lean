import Proofs.Program
import Proofs.Format

namespace LZ4Verification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Case where
  name : String
  input : List Nat
  cap : Nat
  expected : Option (List Nat)
  src : Nat := 131072
  dst : Nat := 262144
  deriving Repr

def initial (src dst n cap : Nat) (m : Memory) : State :=
  { vars := #[src, dst, n, cap] ++ Array.replicate 24 0, mem := m }

def runCase (c : Case) : Option (Nat × State) :=
  execute 20000 vmProgram
    (initial c.src c.dst c.input.length c.cap (putBytes [] c.src c.input))

def within (addr count base len : Nat) : Bool :=
  base ≤ addr && addr+count ≤ base+len

def admissible (c : Case) : Bool :=
  c.input.all (fun b => b < 256) &&
  131072 ≤ c.src && c.src+c.input.length ≤ 2097152 &&
  131072 ≤ c.dst && c.dst+c.cap ≤ 2097152 &&
  (c.src+c.input.length ≤ c.dst || c.dst+c.cap ≤ c.src)

def safeAccess (c : Case) (a : Access) : Bool :=
  if a.write then within a.addr a.count c.dst c.cap
  else within a.addr a.count c.src c.input.length || within a.addr a.count c.dst c.cap

def checkR1 (c : Case) : Bool :=
  match runCase c with
  | none => false
  | some (_, s) => s.trace.all (safeAccess c)

def correctOutput (c : Case) (r : Nat) (s : State) (out : List Nat) : Bool :=
  r == out.length && r ≤ c.cap && getBytes s.mem c.dst r == out

def checkR2 (c : Case) : Bool :=
  match decode c.input with
  | none => true
  | some d =>
    if endConditions d && d.output.length ≤ c.cap then
      match runCase c with
      | none => false
      | some (r, s) => correctOutput c r s d.output
    else true

def checkR3 (c : Case) : Bool :=
  match runCase c with
  | none => false
  | some (r, s) =>
    if r < 2147483648 then
      match decode c.input with
      | none => false
      | some d => correctOutput c r s d.output
    else true

def checkExpected (c : Case) : Bool :=
  match runCase c with
  | none => false
  | some (r, s) =>
    match c.expected with
    | none => r == 4294967295
    | some out => correctOutput c r s out

def checkedCase (c : Case) : Bool :=
  admissible c && checkExpected c && checkR1 c && checkR2 c && checkR3 c


end LZ4Verification
