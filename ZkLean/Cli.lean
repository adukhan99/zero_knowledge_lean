/-
The `zklean` command line.

    zklean seal   MODULE [DECL ...]   seal declarations into obfuscated artifacts
    zklean check  ARTIFACT ...        re-check artifacts with the Lean kernel
    zklean commit MODULE ...          seal everything and commit it to one Merkle root
    zklean export ARTIFACT           re-emit as Lean's NDJSON export format
-/
import ZkLean.Export

namespace ZkLean
open Lean

def usage : String := "\
zklean - seal Lean 4 proofs into obfuscated, kernel-checkable artifacts

USAGE
  zklean seal   MODULE [DECL ...]   seal declarations (default: every theorem in MODULE)
  zklean check  ARTIFACT ...        re-check artifacts with the Lean kernel
  zklean commit MODULE ...          seal everything and commit it to one Merkle root
  zklean export ARTIFACT           re-emit a checked artifact as Lean NDJSON export
                                   format, for independent checkers
  zklean SRC DST                    seal a whole repository into a standalone,
                                   obfuscated one (alias: seal-repo SRC DST)

OPTIONS
  -o, --out DIR            output directory (default: zkl)
      --salt S             fixed salt; reproducible but invertible by anyone who
                           knows S. Default: fresh random salt, printed once.
      --hide-statement     obfuscate the target's statement as well as its proof
      --standalone         carry the whole closure down to `Nat`, so the artifact
                           checks against an empty environment with no Lean install
      --format F           export format: `ndjson` (default, Lean v3.1.0, read by
                           lean4lean / nanoda_lib) or `legacy` (the older
                           line-based format, read by zkPi)
      --include M1,M2      also treat these modules as part of the sealed development
      --allow-axioms A,B   extra axioms `check` will tolerate (default: the three
                           standard ones -- propext, Classical.choice, Quot.sound)
      --help               this message

Run under `lake env` (or `lake exe zklean`) so the Lean search path is set."

structure Opts where
  outDir        : System.FilePath := "zkl"
  salt          : Option String := none
  hideStatement : Bool := false
  standalone    : Bool := false
  legacyFormat  : Bool := false
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
  | "--standalone" :: rest => parseOpts rest { o with standalone := true } pos
  | "--format" :: v :: rest =>
      match v with
      | "ndjson" => parseOpts rest { o with legacyFormat := false } pos
      | "legacy" => parseOpts rest { o with legacyFormat := true } pos
      | _ => throw (IO.userError s!"--format: expected `ndjson` or `legacy`, got {v}")
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

/-- Components Lean uses for declarations it generates itself.

There is no reliable flag for "the elaborator wrote this". `isReservedName`
does not cover the lemmas derived from an inductive type -- it answers false for
`Tree.leaf.injEq` and friends -- and every generated lemma carries a source
position, so declaration ranges do not separate them either. Matching whole name
components is a heuristic, but a conservative one: a component must equal one of
these exactly, so a theorem called `below_diagonal` or `rec_unique` is untouched.

Getting it wrong only affects which declarations are sealed *by default*. A
skipped theorem can always be sealed by naming it: `zklean seal MODULE My.thm`.
-/
def generatedComponents : Array String :=
  #["inj", "injEq", "sizeOf_spec", "noConfusion", "noConfusionType",
    "brecOn", "below", "ibelow", "binductionOn", "rec", "recOn", "casesOn",
    "ndrec", "ndrecOn", "induct", "fun_cases", "eq_def", "eq_zero", "eq_succ"]

/-- Whether `n` looks like something the elaborator generated. -/
def isGeneratedName (n : Name) : Bool :=
  let rec go : Name -> Bool
    | .anonymous => false
    | .num _ _ => true
    | .str p c =>
      generatedComponents.contains c
      -- `eq_1`, `match_3`, `proof_7`, ... are all generated.
      || (["eq_", "match_", "proof_", "unfold_"].any fun pre =>
            c.startsWith pre && !(c.drop pre.length).isEmpty
              && (c.drop pre.length).toString.all Char.isDigit)
      || go p
  go n

/-- Every theorem the sealed development itself declares, excluding private
helpers and anything the elaborator generated (`.injEq`, `.sizeOf_spec`,
equation lemmas, ...). Skipped declarations are still sealed when a target
depends on them; they are just not targets in their own right. -/
def localTheorems (env base : Environment) : Array Name :=
  let ns := env.constants.fold (init := #[]) fun acc n ci =>
    if (findConst? base n).isSome then acc
    else if ci matches .thmInfo _ then
      if n.isInternal || isGeneratedName n || Lean.isReservedName env n
         || Lean.isAuxRecursor env n || Lean.isNoConfusion env n then acc
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
    sealDecl env base target (if o.standalone then #[] else imports)
      { salt, hideStatement := o.hideStatement, standalone := o.standalone }
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
    let scope := if r.standalone then "standalone" else "plus imports"
    IO.println s!"  declarations: {r.declCount} ({scope}; all accepted by the kernel)"
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

/-- Re-emit an artifact in Lean's official NDJSON export format.

The artifact is replayed through the kernel first, so what gets written is
exactly what the kernel accepted -- including the recursors it derived, which a
sealed artifact does not carry. -/
def cmdExport (o : Opts) (pos : Array String) : IO UInt32 := do
  let some (path : String) := pos[0]? | throw (IO.userError s!"export: expected an artifact path\n\n{usage}")
  Lean.initSearchPath (<- Lean.findSysroot)
  let j <- IO.ofExcept (Json.parse (<- IO.FS.readFile path))
  let a <- IO.ofExcept (parseArtifact j)
  let r <- checkArtifact a o.allowAxioms
  unless r.extraAxioms.isEmpty do
    let names := String.intercalate ", " (r.extraAxioms.toList.map toString)
    throw (IO.userError s!"export: refusing {path}; it depends on {names}")
  let baseEnv <- if a.imports.isEmpty then mkEmptyEnvironment
                 else importModules (a.imports.map fun m => { module := m }) {} (trustLevel := 0)
  let env <- Environment.replay
    (Std.HashMap.ofList (a.constants.toList.map fun c => (c.name, c))) baseEnv
  let text <- if o.legacyFormat then IO.ofExcept (exportLegacy env #[a.target])
              else pure (exportNdjson env #[a.target])
  let out := o.outDir / (if o.legacyFormat then s!"{a.target}.export" else s!"{a.target}.ndjson")
  if let some d := out.parent then IO.FS.createDirAll d
  IO.FS.writeFile out text
  IO.println s!"target      : {a.target}"
  IO.println s!"standalone  : {r.standalone}"
  let lineCount := (text.splitOn "\n").length - 1
  IO.println s!"lines       : {lineCount}"
  IO.println s!"export      : {out}"
  return 0

/-- The Lake package root at or above `p`: the nearest directory holding a
`lakefile.toml` or `lakefile.lean`. Module names are relative to this, not to
whatever subdirectory the user pointed at, so `zklean ZkLean out` still yields
`ZkLean.Check` rather than `Check`. -/
partial def packageRoot (p : System.FilePath) : IO System.FilePath := do
  let cur <- IO.FS.realPath p
  let rec up (d : System.FilePath) (fuel : Nat) : IO System.FilePath := do
    match fuel with
    | 0 => return cur
    | fuel + 1 =>
      if (<- (d / "lakefile.toml").pathExists) || (<- (d / "lakefile.lean").pathExists) then
        return d
      match d.parent with
      | some par => if par == d then return cur else up par fuel
      | none => return cur
  up (if (<- cur.isDir) then cur else cur.parent.getD cur) 64

/-- Every `.lean` file under `dir`, as module names relative to `root`. Skips
build and VCS directories. -/
partial def discoverModules (root dir : System.FilePath) : IO (Array Name) := do
  let skip := [".lake", ".git", "build", "lake-packages", "node_modules"]
  let rootStr := (<- IO.FS.realPath root).toString
  let rec go (p : System.FilePath) : IO (Array Name) := do
    let mut acc : Array Name := #[]
    for e in (<- p.readDir) do
      let base := e.fileName
      if base.startsWith "." || skip.contains base then continue
      if (<- e.path.isDir) then
        acc := acc ++ (<- go e.path)
      else if base.endsWith ".lean" then
        let full := (<- IO.FS.realPath e.path).toString
        if full.startsWith rootStr then
          let rel := ((full.drop (rootStr.length + 1)).toString.dropEnd 5).toString
          let parts := (rel.splitOn "/").filter (fun c => !c.isEmpty)
          unless parts.isEmpty do
            acc := acc.push (parts.foldl (fun n c => Name.str n c) Name.anonymous)
    return acc
  let mods <- go (<- IO.FS.realPath dir)
  return mods.qsort (fun a b => a.toString < b.toString)

/-- `zklean SRC DST`: turn a Lean repository into a self-contained,
kernel-checkable, obfuscated one.

This is the headline operation, and it is one-way by construction: the output
holds elaborated proof terms with every name the development introduced
replaced by a salt-keyed digest, and the salt is discarded unless you asked for
a fixed one. Nothing in `DST` can reconstruct `SRC`.

Run it under the *source* repository's `lake env` so its modules are on the
search path:

    lake env /path/to/zklean . ../zk-repo
-/
def cmdSealRepo (o : Opts) (src dst : System.FilePath) : IO UInt32 := do
  let root <- packageRoot src
  let mods <- discoverModules root src
  if mods.isEmpty then
    IO.eprintln s!"no .lean files under {src}"
    return 1
  IO.println s!"source      : {src}  ({mods.size} modules, package root {root})"
  let (env, base, _) <- loadEnvs mods o.include?
  let targets := localTheorems env base
  if targets.isEmpty then
    IO.eprintln "no theorems found; is the source repository built?"
    return 1
  let salt <- match o.salt with | some s => pure s | none => freshSalt
  let saltNote := if o.salt.isSome then "fixed (reproducible, and invertible by anyone holding it)"
                  else "random, and discarded -- the mapping is not recoverable"
  -- Everything is sealed standalone: the output must not need a Lean install.
  let opts := { o with standalone := true, outDir := dst }
  let mut entries : Array (String × String) := #[]
  let mut sealedCount := 0
  let mut refused : Array Name := #[]
  for t in targets do
    try
      let (_, text, sealed) <- sealOne env base #[] t opts salt
      entries := entries.push (s!"thm:{sealed.target}", text)
      sealedCount := sealedCount + 1
    catch e =>
      refused := refused.push t
      IO.eprintln s!"skipped {t}: {e}"
  let (root, sorted, proofs) := commit entries
  let leaves := (Array.range sorted.size).map fun i =>
    let (id, content) := sorted[i]!
    Json.mkObj [
      ("id", Json.str id),
      ("content_hash", Json.str (toHex (leafHash content))),
      ("artifact", Json.str ((id.drop 4).toString ++ ".zkl.json")),
      ("proof", Json.arr (proofs[i]!.map fun st =>
        Json.mkObj [("sibling", Json.str (toHex st.sibling)), ("left", Json.bool st.left)]))]
  let transcript := Json.mkObj [
    ("format", Json.str "zklean/v2"),
    ("hash", Json.str "sha256"),
    ("standalone", Json.bool true),
    ("domain_separation", Json.mkObj [
      ("leaf", Json.str "SHA256(0x00 || utf8(content))"),
      ("node", Json.str "SHA256(0x01 || left || right)"),
      ("empty", Json.str "SHA256(0x00)")]),
    ("root", Json.str (toHex root)),
    ("leaf_count", Json.num (JsonNumber.fromNat sorted.size)),
    ("leaves", Json.arr leaves)]
  let _ <- writeJson (dst / "transcript.json") transcript
  IO.println s!"theorems    : {sealedCount} sealed{if refused.isEmpty then "" else s!", {refused.size} skipped"}"
  IO.println s!"salt        : {saltNote}"
  IO.println s!"merkle root : {toHex root}"
  IO.println s!"output      : {dst}"
  return if sealedCount == 0 then 1 else 0

def run (argv : List String) : IO UInt32 := do
  match argv with
  | [] | ["--help"] | ["-h"] => IO.println usage; return 0
  | cmd :: rest =>
    let (o, pos) <- parseOpts rest
    match cmd with
    | "seal" => cmdSeal o pos
    | "check" => cmdCheck o pos
    | "commit" => cmdCommit o pos
    | "export" => cmdExport o pos
    | "seal-repo" =>
      match (pos[0]? : Option String), (pos[1]? : Option String) with
      | some a, some b => cmdSealRepo o a b
      | _, _ => IO.eprintln s!"seal-repo: expected SRC and DST\n\n{usage}"; return 1
    | _ =>
      -- `zklean SRC DST` is the headline form; treat it as `seal-repo`.
      if (<- (cmd : System.FilePath).isDir) && pos.size == 1 then
        cmdSealRepo o cmd pos[0]!
      else
        IO.eprintln s!"unknown command: {cmd}\n\n{usage}"
        return 1

end ZkLean
