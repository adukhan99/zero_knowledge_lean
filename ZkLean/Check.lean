/-
Verification: re-check a sealed artifact with the real Lean kernel.

Nothing in this file decides whether a proof is correct. It decodes the
artifact, hands every declaration to `Lean.Environment.replay` -- which sends
each one to the kernel at trust level 0 -- and then audits what the kernel
accepted. The trusted base is therefore exactly the Lean kernel, the same base
you trust when you run `lake build` on the original repository.

The audit after replay matters as much as the replay itself: an artifact is
free to contain `axiom fake : False`, and the kernel will happily accept it.
`checkArtifact` therefore reports every axiom the target transitively depends
on and rejects anything outside the caller's allowlist.
-/
import ZkLean.Seal

namespace ZkLean
open Lean

/-- The three axioms of Lean's standard classical foundation. Anything else in
a sealed artifact is a new assumption and must be surfaced. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

structure Artifact where
  target        : Name
  statementHash : String
  imports       : Array Name
  root          : String
  constants     : Array ConstantInfo

/-- Decode an artifact. Rejects anything the wire format refuses (open terms,
unsafe or partial declarations) and any duplicate declaration. -/
def parseArtifact (j : Json) : Res Artifact := do
  let fmt <- (<- j.getObjVal? "format").getStr?
  if fmt != "zklean-seal/v1" then throw s!"unsupported artifact format: {fmt}"
  let target <- nameOfJson (<- j.getObjVal? "target")
  let statementHash <- (<- j.getObjVal? "statement_hash").getStr?
  let root <- (<- j.getObjVal? "root").getStr?
  let imports <- (<- (<- j.getObjVal? "imports").getArr?).mapM nameOfJson
  let constants <- (<- (<- j.getObjVal? "constants").getArr?).mapM constOfJson
  let mut seen : NameSet := {}
  for c in constants do
    if seen.contains c.name then throw s!"artifact declares {c.name} twice"
    seen := seen.insert c.name
  return { target, statementHash, imports, root, constants }

/-- Recompute the Merkle root over the artifact's declarations. Re-encoding the
*decoded* constants also proves the wire codec round-trips exactly. -/
def artifactRoot (a : Artifact) : Res String := do
  let entries <- a.constants.mapM fun c => return (c.name.toString, (<- constToJson c).compress)
  let (root, _, _) := commit entries
  return toHex root

/-- Re-serialise an artifact, recomputing its Merkle root and statement hash
from the declarations it currently holds.

This is what an honest prover does, and therefore what a *dishonest* one does
too: neither the commitment nor the statement digest is evidence that a proof
is correct, since anyone editing the declarations can simply recompute both.
Only the kernel replay and the axiom audit carry weight. The test suite uses
this to build tampered artifacts that are internally consistent, so the
rejection it then expects can only come from the kernel. -/
def Artifact.reseal (a : Artifact) : Res Json := do
  let encoded <- a.constants.mapM fun c => return (c.name, <- constToJson c)
  let (root, _, _) := commit (encoded.map fun e => (e.1.toString, e.2.compress))
  let some target := a.constants.find? fun c => c.name == a.target
    | throw s!"artifact does not define its own target {a.target}"
  let stmtHash := toHex (sha256s (<- exprToJson target.type).compress)
  return Json.mkObj [
    ("format", Json.str "zklean-seal/v1"),
    ("hash", Json.str "sha256"),
    ("target", nameToJson a.target),
    ("statement_hash", Json.str stmtHash),
    ("imports", Json.arr (a.imports.map nameToJson)),
    ("root", Json.str (toHex root)),
    ("constants", Json.arr (encoded.map fun e => e.2))]

/-- Axioms `n` transitively depends on, over a fully replayed environment. -/
def axiomsUsed (env : Environment) (n : Name) : Array Name :=
  (localClosure env (fun _ => true) #[n]).toArray.filter fun m =>
    match findConst? env m with
    | some (.axiomInfo _) => true
    | _ => false

/-- Drop the banner `pp.rawOnError` prepends when it falls back.

The delaborator resolves constants through `Environment.find?`, which cannot see
what `replay` added (see `findConst?`), so any statement mentioning one of the
artifact's own declarations takes the raw path. The raw rendering is complete
and correct; only the banner is noise. -/
private def stripRawBanner (s : String) : String :=
  if s.startsWith "[Error pretty printing expression:" then
    match s.splitOn "]\n" with
    | _ :: rest => String.intercalate "]\n" rest |>.trimAscii.toString
    | [] => s
  else s

/-- Render a statement for display.

Two deliberate choices here. The expression is rendered against the *replayed*
environment, which is the only one that knows the artifact's own constants; and
`pp.rawOnError` is set so an expression the delaborator cannot handle falls back
to fully explicit form instead of failing.

`Environment.replay` returns a bare kernel environment with no notation tables,
so statements print in explicit application form (`Eq (f x) y`, not `f x = y`).
That is a little verbose, and for a verifier it is the safer default: explicit
form cannot be disguised by redefined notation, so what you read is exactly what
the kernel checked. -/
def ppForDisplay (env : Environment) (levelParams : List Name) (e : Expr) : IO String := do
  let opts := ({} : Options).setBool `pp.rawOnError true
  let ctx : Core.Context := { fileName := "<zklean>", fileMap := default, options := opts }
  let body <-
    try
      let (fmt, _) <- (Lean.Meta.MetaM.run' (Lean.Meta.ppExpr e)).toIO ctx { env }
      pure (stripRawBanner (toString fmt))
    catch _ => pure (toString e)
  if levelParams.isEmpty then return body
  return "{" ++ String.intercalate " " (levelParams.map toString) ++ "} " ++ body

structure Report where
  standalone : Bool
  target     : Name
  statement  : String
  axioms     : Array Name
  extraAxioms : Array Name
  declCount  : Nat
  rootOk     : Bool
  root       : String

/-- Full verification: commitment, kernel replay, statement binding, axiom
audit. Throws on the first failure; a returned `Report` means the kernel
accepted every declaration. -/
def checkArtifact (a : Artifact) (allowed : Array Name) : IO Report := do
  let recomputed <- IO.ofExcept (artifactRoot a)
  if recomputed != a.root then
    throw <| IO.userError
      s!"commitment mismatch: artifact claims root {a.root} but its declarations hash to {recomputed}"

  -- An empty import list means a standalone witness: everything it needs is in
  -- the file, and it is checked against a literally empty environment. That is
  -- the property any zero-knowledge backend depends on, since a prover running
  -- in a circuit or a zkVM cannot open `.olean` files.
  let baseEnv <- if a.imports.isEmpty then mkEmptyEnvironment
                 else importModules (a.imports.map fun m => { module := m }) {} (trustLevel := 0)
  for c in a.constants do
    if (findConst? baseEnv c.name).isSome then
      throw <| IO.userError s!"artifact redefines an imported constant: {c.name}"

  -- The kernel checks everything here.
  let env <- Environment.replay (Std.HashMap.ofList (a.constants.toList.map fun c => (c.name, c)))
    baseEnv

  let some ci := findConst? env a.target
    | throw <| IO.userError s!"artifact does not define its own target {a.target}"
  unless ci matches .thmInfo _ do
    throw <| IO.userError s!"target {a.target} is not a theorem"

  let stmtDigest := (<- IO.ofExcept (exprToJson ci.type)).compress
  let stmtHash := toHex (sha256s stmtDigest)
  if stmtHash != a.statementHash then
    throw <| IO.userError
      s!"statement mismatch: artifact claims {a.statementHash} but its target's type hashes to {stmtHash}"

  let axs := axiomsUsed env a.target
  let extra := axs.filter fun n => !allowed.contains n
  return { standalone := a.imports.isEmpty, target := a.target,
           statement := <- ppForDisplay env ci.levelParams ci.type,
           axioms := axs,
           extraAxioms := extra, declCount := a.constants.size, rootOk := true,
           root := a.root }

end ZkLean
