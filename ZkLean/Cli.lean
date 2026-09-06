/-
The `zklean` command line.

    zklean seal   MODULE [DECL ...]   seal declarations into obfuscated artifacts
    zklean check  ARTIFACT ...        re-check artifacts with the Lean kernel
    zklean commit MODULE ...          seal everything and commit it to one Merkle root
-/
import ZkLean.Check

namespace ZkLean
open Lean

def usage : String := "\
zklean - seal Lean 4 proofs into obfuscated, kernel-checkable artifacts

USAGE
  zklean seal   MODULE [DECL ...]   seal declarations (default: every theorem in MODULE)
  zklean check  ARTIFACT ...        re-check artifacts with the Lean kernel
  zklean commit MODULE ...          seal everything and commit it to one Merkle root

OPTIONS
  -o, --out DIR            output directory (default: zkl)
      --salt S             fixed salt; reproducible but invertible by anyone who
                           knows S. Default: fresh random salt, printed once.
      --hide-statement     obfuscate the target's statement as well as its proof
      --include M1,M2      also treat these modules as part of the sealed development
      --allow-axioms A,B   extra axioms `check` will tolerate (default: the three
                           standard ones -- propext, Classical.choice, Quot.sound)
      --help               this message

Run under `lake env` (or `lake exe zklean`) so the Lean search path is set."

structure Opts where
  outDir        : System.FilePath := "zkl"
  salt          : Option String := none
  hideStatement : Bool := false
  include?      : Array Name := #[]
  allowAxioms   : Array Name := standardAxioms

/-- 32 bytes of entropy, hex encoded. Falls back to a clock-derived salt where
`/dev/urandom` is unavailable, with a warning, since a guessable salt makes the
name mangling invertible. -/
def freshSalt : IO String := do
  try
    let h <- IO.FS.Handle.mk "/dev/urandom" .read
    return toHex (<- h.read 32)
  catch _ =>
    IO.eprintln "warning: no /dev/urandom; falling back to a low-entropy salt"
    return toHex (sha256s (toString (<- IO.monoNanosNow)))

private def splitNames (s : String) : Array Name :=
  (s.splitOn ",").toArray.filterMap fun p =>
    let p := p.trimAscii.toString
    if p.isEmpty then none else some (p.toName)

/-- Parse flags, returning them alongside the positional arguments. -/
partial def parseOpts (args : List String) (o : Opts := {}) (pos : Array String := #[]) :
    IO (Opts × Array String) := do
  match args with
  | [] => return (o, pos)
  | "-o" :: v :: rest | "--out" :: v :: rest => parseOpts rest { o with outDir := v } pos
  | "--salt" :: v :: rest => parseOpts rest { o with salt := some v } pos
  | "--hide-statement" :: rest => parseOpts rest { o with hideStatement := true } pos
  | "--include" :: v :: rest => parseOpts rest { o with include? := splitNames v } pos
  | "--allow-axioms" :: v :: rest =>
      parseOpts rest { o with allowAxioms := standardAxioms ++ splitNames v } pos
  | a :: rest =>
      if a.startsWith "-" then throw (IO.userError s!"unknown option: {a}\n\n{usage}")
      else parseOpts rest o (pos.push a)

/-- Import `mods`, and separately import everything they transitively depend on
*except* themselves. The difference between the two environments is exactly the
development being sealed. -/
def loadEnvs (mods : Array Name) (extra : Array Name) :
    IO (Environment × Environment × Array Name) := do
  Lean.initSearchPath (<- Lean.findSysroot)
  let env <- importModules (mods.map fun m => { module := m }) {} (trustLevel := 0)
  let sealedMods := mods ++ extra
  let all := env.header.modules.map fun m => m.module
  let baseMods := all.filter fun m => !sealedMods.contains m
  let base <- importModules (baseMods.map fun m => { module := m }) {} (trustLevel := 0)
  -- An artifact should name the smallest import set that supplies its external
  -- constants: the direct imports of the sealed modules, minus the sealed
  -- modules themselves.
  let mut direct : Array Name := #[]
  for i in [:all.size] do
    if sealedMods.contains all[i]! then
      if h : i < env.header.moduleData.size then
        for imp in env.header.moduleData[i].imports do
          if !sealedMods.contains imp.module && !direct.contains imp.module then
            direct := direct.push imp.module
  return (env, base, if direct.isEmpty then #[`Init] else direct)

/-- Every theorem the sealed development itself declares, excluding the ones
the elaborator generates (`.injEq`, `.sizeOf_spec`, equation lemmas, ...) and
private helpers. Those are still sealed when a target depends on them; they are
just not targets in their own right. -/
def localTheorems (env base : Environment) : Array Name :=
  let ns := env.constants.fold (init := #[]) fun acc n ci =>
    if (findConst? base n).isSome then acc
    else if ci matches .thmInfo _ then
      if n.isInternal || Lean.isReservedName env n || Lean.isAuxRecursor env n
         || Lean.isNoConfusion env n then acc
      else acc.push n
    else acc
  ns.qsort (fun a b => a.toString < b.toString)

/-- Write `j` and return the exact text written.

A transcript commits to these bytes verbatim rather than to a re-canonicalised
form, so a verifier in any language hashes the file it was given and needs no
knowledge of how Lean serialises JSON. Formatting cannot be used to smuggle
anything past this: `zklean check` independently recomputes the artifact's own
Merkle root from the decoded declarations, so the content is pinned twice. -/
def writeJson (path : System.FilePath) (j : Json) : IO String := do
  if let some d := path.parent then IO.FS.createDirAll d
  let text := j.pretty ++ "\n"
  IO.FS.writeFile path text
  return text

/-- Warn if a sealed proof rests on anything beyond Lean's standard three
axioms. `check` will refuse it later; saying so now saves the round trip. -/
def warnAxioms (target : Name) (s : Sealed) : IO Unit := do
  let extra := s.axioms.filter fun n => !standardAxioms.contains n
  unless extra.isEmpty do
    let names := String.intercalate ", " (extra.toList.map toString)
    if extra.contains ``sorryAx then
      IO.eprintln s!"warning: {target} is proved with `sorry`; `zklean check` will reject it"
    else
      IO.eprintln s!"warning: {target} depends on non-standard axioms ({names}); \
`zklean check` will reject it unless run with --allow-axioms"

/-- Seal one declaration and write its artifact; returns the path and the exact
text written (which is what a transcript commits to). -/
def sealOne (env base : Environment) (imports : Array Name) (target : Name) (o : Opts)
    (salt : String) : IO (System.FilePath × String × Sealed) := do
  let s <- IO.ofExcept <|
    sealDecl env base target imports { salt, hideStatement := o.hideStatement }
  let path := o.outDir / s!"{s.target}.zkl.json"
  let text <- writeJson path s.toJson
  warnAxioms target s
  return (path, text, s)

def cmdSeal (o : Opts) (pos : Array String) : IO UInt32 := do
  let some modName := pos[0]? | throw (IO.userError s!"seal: expected a module name\n\n{usage}")
  let mods := #[modName.toName]
  let (env, base, imports) <- loadEnvs mods o.include?
  let targets := if pos.size > 1 then (pos.extract 1 pos.size).map (·.toName)
                 else localTheorems env base
  if targets.isEmpty then
    IO.eprintln s!"seal: no theorems found in {modName}"
    return 1
  let salt <- match o.salt with | some s => pure s | none => freshSalt
  if o.salt.isNone then
    IO.println s!"salt        : {salt}  (keep this to re-derive the mapping)"
  for t in targets do
    let (path, _, s) <- sealOne env base imports t o salt
    IO.println s!"{t}"
    IO.println s!"  sealed as : {s.target}"
    IO.println s!"  hidden    : {s.hiddenCount} declarations   public: {s.publicCount}"
    IO.println s!"  root      : {s.root}"
    IO.println s!"  artifact  : {path}"
  return 0

/-- Verify one artifact and print a single verdict for it.

Exactly one of `VALID` / `REJECTED` / `INVALID` is printed per artifact, and it
comes first: an artifact whose kernel replay succeeds but whose axiom audit
fails is `REJECTED`, never `VALID` with a caveat underneath. -/
def reportOne (path : System.FilePath) (allowed : Array Name) : IO Bool := do
  let res <- try
      let j <- IO.ofExcept (Json.parse (<- IO.FS.readFile path))
      let a <- IO.ofExcept (parseArtifact j)
      Except.ok <$> checkArtifact a allowed
    catch e => pure (Except.error (toString e))
  match res with
  | .error msg =>
    IO.println s!"INVALID  {path}"
    IO.println s!"  {msg}"
    return false
  | .ok r =>
    let names := fun (a : Array Name) => String.intercalate ", " (a.toList.map toString)
    let ok := r.extraAxioms.isEmpty
    IO.println s!"{if ok then "VALID   " else "REJECTED"} {path}"
    IO.println s!"  target      : {r.target}"
    IO.println s!"  statement   : {r.statement}"
    IO.println s!"  declarations: {r.declCount} (all accepted by the kernel)"
    IO.println s!"  root        : {r.root}"
    IO.println s!"  axioms      : {if r.axioms.isEmpty then "none" else names r.axioms}"
    unless ok do
      if r.extraAxioms.contains ``sorryAx then
        IO.println "  reason      : the proof is incomplete -- it depends on `sorry`"
      else
        IO.println s!"  reason      : depends on assumptions outside the standard three: {names r.extraAxioms}"
      IO.println "                the kernel accepted this term, but it does not prove the statement"
      IO.println "                from Lean's usual foundation. Pass --allow-axioms to permit them."
    return ok

def cmdCheck (o : Opts) (pos : Array String) : IO UInt32 := do
  if pos.isEmpty then throw (IO.userError s!"check: expected an artifact path\n\n{usage}")
  Lean.initSearchPath (<- Lean.findSysroot)
  let mut ok := true
  for p in pos do
    unless <- reportOne p o.allowAxioms do ok := false
  return if ok then 0 else 1

def cmdCommit (o : Opts) (pos : Array String) : IO UInt32 := do
  if pos.isEmpty then throw (IO.userError s!"commit: expected a module name\n\n{usage}")
  let mods := pos.map (·.toName)
  let (env, base, imports) <- loadEnvs mods o.include?
  let targets := localTheorems env base
  let salt <- match o.salt with | some s => pure s | none => freshSalt
  if o.salt.isNone then
    IO.println s!"salt        : {salt}  (keep this to re-derive the mapping)"
  let mut entries : Array (String × String) := #[]
  let mut paths : Array (String × System.FilePath) := #[]
  for t in targets do
    let (path, text, s) <- sealOne env base imports t o salt
    entries := entries.push (s!"thm:{s.target}", text)
    paths := paths.push (s!"thm:{s.target}", path)
  let (root, sorted, proofs) := commit entries
  let leaves := (Array.range sorted.size).map fun i =>
    let (id, content) := sorted[i]!
    let artifact : String := match paths.find? (fun p => p.1 == id) with
      | some (_, p) => p.toString
      | none => ""
    Json.mkObj [
      ("id", Json.str id),
      ("content_hash", Json.str (toHex (leafHash content))),
      ("artifact", Json.str artifact),
      ("proof", Json.arr (proofs[i]!.map fun st =>
        Json.mkObj [("sibling", Json.str (toHex st.sibling)), ("left", Json.bool st.left)]))]
  let transcript := Json.mkObj [
    ("format", Json.str "zklean/v2"),
    ("hash", Json.str "sha256"),
    ("domain_separation", Json.mkObj [
      ("leaf", Json.str "SHA256(0x00 || utf8(content))"),
      ("node", Json.str "SHA256(0x01 || left || right)"),
      ("empty", Json.str "SHA256(0x00)")]),
    ("root", Json.str (toHex root)),
    ("leaf_count", Json.num (JsonNumber.fromNat sorted.size)),
    ("leaves", Json.arr leaves)]
  let tpath := o.outDir / "transcript.json"
  let _ <- writeJson tpath transcript
  IO.println s!"theorems    : {sorted.size}"
  IO.println s!"merkle root : {toHex root}"
  IO.println s!"transcript  : {tpath}"
  return 0

def run (argv : List String) : IO UInt32 := do
  match argv with
  | [] | ["--help"] | ["-h"] => IO.println usage; return 0
  | cmd :: rest =>
    let (o, pos) <- parseOpts rest
    match cmd with
    | "seal" => cmdSeal o pos
    | "check" => cmdCheck o pos
    | "commit" => cmdCommit o pos
    | _ => IO.eprintln s!"unknown command: {cmd}\n\n{usage}"; return 1

end ZkLean
