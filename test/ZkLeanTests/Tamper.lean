/-
A deliberately dishonest prover, used by the test suite.

Each mutation edits a sealed artifact and then *recomputes the commitment and
the statement digest correctly*, so the result is internally consistent: the
Merkle root matches its declarations and the statement hash matches its target's
type. Nothing short of the Lean kernel can tell these apart from honest
artifacts, which is the point -- it pins down what `zklean check` is actually
relying on.

    zklean-tamper replace-proof  IN OUT        target's proof term := True.intro
    zklean-tamper swap-statement IN OTHER OUT  target's type := OTHER's target type
-/
import ZkLean.Check

open Lean ZkLean

/-- Replace the target's proof with `True.intro`, which proves the wrong thing. -/
def replaceProof (a : Artifact) : Artifact :=
  { a with constants := a.constants.map fun c =>
      if c.name != a.target then c
      else match c with
        | .thmInfo v => .thmInfo { v with value := .const ``True.intro [] }
        | other => other }

/-- Give the target someone else's statement while keeping its own proof. -/
def swapStatement (a other : Artifact) : Except String Artifact := do
  let some src := other.constants.find? fun c => c.name == other.target
    | throw "donor artifact does not define its own target"
  return { a with constants := a.constants.map fun c =>
    if c.name != a.target then c
    else match c with
      | .thmInfo v =>
        .thmInfo { v with toConstantVal :=
          { v.toConstantVal with type := src.type, levelParams := src.levelParams } }
      | other => other }

def readArtifact (p : String) : IO Artifact := do
  IO.ofExcept (parseArtifact (<- IO.ofExcept (Json.parse (<- IO.FS.readFile p))))

def writeArtifact (p : String) (a : Artifact) : IO Unit := do
  IO.FS.writeFile p ((<- IO.ofExcept a.reseal).pretty ++ "\n")

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (<- Lean.findSysroot)
  match args with
  | ["replace-proof", inp, out] =>
      writeArtifact out (replaceProof (<- readArtifact inp)); return 0
  | ["swap-statement", inp, donor, out] =>
      let a <- readArtifact inp
      let d <- readArtifact donor
      writeArtifact out (<- IO.ofExcept (swapStatement a d)); return 0
  | _ => IO.eprintln "usage: zklean-tamper (replace-proof IN OUT | swap-statement IN OTHER OUT)"
         return 1
