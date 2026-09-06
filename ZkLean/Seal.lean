/-
Sealing: turn a checked Lean declaration into an obfuscated, self-contained
artifact that the Lean kernel can still re-check.

What sealing removes
--------------------
* all source text: comments, docstrings, tactic scripts, file and line
  structure -- only the *elaborated* proof term survives;
* every name introduced by the sealed development, replaced by a salt-keyed
  opaque identifier (`_zk<hex>`);
* every binder name and every `Expr.mdata` annotation;
* every universe parameter name, renumbered positionally;
* every declaration in the repository that the target does not depend on.

What sealing preserves
----------------------
* exact kernel semantics: the renaming is an injective substitution and the
  erasures are annotations the kernel ignores, so the artifact type-checks iff
  the original did;
* by default the target's *statement* -- its type, and the definitions that
  type mentions -- so a verifier can read what was proved while learning
  nothing about how. `hideStatement` obfuscates that too.
-/
import ZkLean.Wire
import ZkLean.Merkle

namespace ZkLean
open Lean

/-- Look a constant up in `env`, including declarations `Environment.replay`
has just added.

`Environment.find?` consults the imported constant map and the async branches
only, so on a replayed environment it reports every freshly kernel-checked
declaration as missing. Using it for the axiom audit would make that audit
vacuously pass, so every lookup in this tool goes through here. -/
def findConst? (env : Environment) (n : Name) : Option ConstantInfo :=
  env.constants.find?' n

/-- Names reachable from `roots`, restricted to those `isLocal` accepts. -/
partial def localClosure (env : Environment) (isLocal : Name -> Bool) (roots : Array Name) :
    NameSet :=
  roots.foldl (init := {}) fun acc r => go acc r
where
  go (acc : NameSet) (n : Name) : NameSet :=
    if acc.contains n || !isLocal n then acc
    else match findConst? env n with
      | none => acc
      | some ci =>
        let acc := acc.insert n
        let acc := ci.getUsedConstantsAsSet.foldl (fun a m => go a m) acc
        -- An inductive drags in its constructors and recursors, and vice versa.
        match ci with
        | .inductInfo v => (v.ctors ++ v.all).foldl go acc
        | .ctorInfo v => go acc v.induct
        | .recInfo v => v.all.foldl go acc
        | _ => acc

/-- Rewrite every name occurring in a `Level`. -/
partial def mapLevel (f : Name -> Name) : Level -> Level
  | .zero => .zero
  | .succ l => .succ (mapLevel f l)
  | .max a b => .max (mapLevel f a) (mapLevel f b)
  | .imax a b => .imax (mapLevel f a) (mapLevel f b)
  | .param n => .param (f n)
  | l@(.mvar _) => l

/-- The single placeholder every binder is renamed to. -/
def binderPlaceholder : Name := `x

/-- Rewrite constant names and universe parameters, erase binder names and drop
`mdata`. All four are invisible to the kernel, so this preserves typing. -/
partial def scrubExpr (fc : Name -> Name) (fl : Name -> Name) : Expr -> Expr
  | .const n us => .const (fc n) (us.map (mapLevel fl))
  | .sort l => .sort (mapLevel fl l)
  | .app a b => .app (scrubExpr fc fl a) (scrubExpr fc fl b)
  | .lam _ t b bi => .lam binderPlaceholder (scrubExpr fc fl t) (scrubExpr fc fl b) bi
  | .forallE _ t b bi => .forallE binderPlaceholder (scrubExpr fc fl t) (scrubExpr fc fl b) bi
  | .letE _ t v b nd =>
      .letE binderPlaceholder (scrubExpr fc fl t) (scrubExpr fc fl v) (scrubExpr fc fl b) nd
  | .proj s i e => .proj (fc s) i (scrubExpr fc fl e)
  | .mdata _ e => scrubExpr fc fl e
  | e => e

/-- Apply a constant renaming throughout a declaration, renumbering its
universe parameters. Universe parameters are positional at use sites, so they
can be renumbered independently in every declaration. -/
def scrubConst (fc : Name -> Name) (ci : ConstantInfo) : ConstantInfo :=
  let lps := ci.levelParams
  let fresh := (List.range lps.length).map fun i => Name.mkSimple s!"u{i}"
  let lmap := Std.HashMap.ofList (lps.zip fresh)
  let fl := fun n => lmap.getD n n
  let e := scrubExpr fc fl
  let cv : ConstantVal := { name := fc ci.name, levelParams := fresh, type := e ci.type }
  match ci with
  | .axiomInfo v => .axiomInfo { v with toConstantVal := cv }
  | .thmInfo v => .thmInfo { v with toConstantVal := cv, value := e v.value, all := v.all.map fc }
  | .defnInfo v => .defnInfo { v with toConstantVal := cv, value := e v.value, all := v.all.map fc }
  | .opaqueInfo v =>
      .opaqueInfo { v with toConstantVal := cv, value := e v.value, all := v.all.map fc }
  | .inductInfo v =>
      .inductInfo { v with toConstantVal := cv, all := v.all.map fc, ctors := v.ctors.map fc }
  | .ctorInfo v => .ctorInfo { v with toConstantVal := cv, induct := fc v.induct }
  | .recInfo v =>
      let rules := v.rules.map fun r => { r with ctor := fc r.ctor, rhs := e r.rhs }
      .recInfo { v with toConstantVal := cv, all := v.all.map fc, rules }
  | .quotInfo v => .quotInfo { v with toConstantVal := cv }

/-- Salt-keyed opaque name for `n`. Without the salt, recovering `n` is a
preimage search over SHA-256; with it, it is a lookup. -/
def opaqueName (salt : String) (n : Name) : Name :=
  Name.mkSimple ("_zk" ++ (toHex (sha256s (salt ++ " " ++ n.toString))).take 16)

structure SealOpts where
  /-- Obfuscate the target's statement as well as its proof. -/
  hideStatement : Bool := false
  /-- Carry the *entire* transitive closure, down to `Nat` and `Eq`, so the
  artifact can be checked against an empty environment with no Lean
  installation at all.

  This is what any zero-knowledge backend needs: a prover running inside a
  circuit or a zkVM gets a byte array and cannot open `.olean` files. It is
  also why standalone artifacts do not obfuscate imported names -- see
  `mayRename` in `sealDecl`. -/
  standalone : Bool := false
  /-- Keys the name mangling. A fresh random salt makes the mangling
  non-invertible; a fixed salt makes sealing reproducible. -/
  salt : String

structure Sealed where
  target        : Name
  statementHash : String
  imports       : Array Name
  /-- Axioms the target depends on, computed at seal time. Reported to the
  prover as a warning; deliberately *not* written into the artifact, because a
  verifier must recompute it rather than believe it. -/
  axioms        : Array Name
  constants     : Array (Name × Json)
  root          : String
  hiddenCount   : Nat
  publicCount   : Nat

/-- Number of components in a name, used to order parents before children. -/
private def nameDepth : Name -> Nat
  | .anonymous => 0
  | .str p _ => nameDepth p + 1
  | .num p _ => nameDepth p + 1

/-- Build the renaming applied to a sealed development.

Renaming has to respect Lean's naming convention for generated declarations:
the kernel regenerates an inductive's recursor as `<inductive>.rec`, so if `T`
becomes `_zkab..`, then `T.rec` must become `_zkab...rec` and not some
unrelated opaque name. The map is therefore built parent-first, and a name
whose parent was renamed inherits that parent's new prefix.

A name in `publicSet` keeps its own name -- but only if its parent did too,
which always holds, since anything the target's type mentions has its parents
in the type's closure as well. -/
def buildRenameMap (salt : String) (closure publicSet : NameSet)
    (isRecursor : Name -> Bool) (mayRename : Name -> Bool) :
    Res (Std.HashMap Name Name) := do
  let ordered := closure.toArray.qsort fun a b =>
    let da := nameDepth a
    let db := nameDepth b
    if da != db then da < db else a.toString < b.toString
  let mut m : Std.HashMap Name Name := {}
  let mut taken : Std.HashMap Name Name := {}
  for n in ordered do
    let parentRenamed : Option Name :=
      match n with
      | .str p c => match m[p]? with
                    | some p' => if p' == p then none else some (Name.str p' c)
                    | none => none
      | .num p i => match m[p]? with
                    | some p' => if p' == p then none else some (Name.num p' i)
                    | none => none
      | .anonymous => none
    let r :=
      if !mayRename n then
        -- Imported constants keep their names. Some are privileged by the
        -- kernel (`Nat` and friends back literal arithmetic), the three
        -- standard axioms must stay recognisable to the audit, and none of
        -- them is yours to hide anyway.
        n
      else if isRecursor n then
        -- The kernel derives this name itself when it replays the inductive,
        -- so it must track the inductive's name whether or not that changed.
        match n with
        | .str p c => Name.str (m.getD p p) c
        | .num p i => Name.num (m.getD p p) i
        | .anonymous => n
      else match parentRenamed with
        | some r => r
        | none => if publicSet.contains n then n else opaqueName salt n
    if let some other := taken[r]? then
      throw s!"name collision under this salt: {other} and {n} both map to {r}"
    taken := taken.insert r n
    m := m.insert n r
  return m

/-- Seal `target` out of `env`. Any constant absent from `base` counts as part
of the sealed development and is therefore exported (and possibly renamed);
constants present in `base` are left alone and reached through `imports`. -/
def sealDecl (env base : Environment) (target : Name) (imports : Array Name) (o : SealOpts) :
    Res Sealed := do
  -- Two separate questions. `inClosure`: does this constant travel with the
  -- artifact, or is it reached through an import? `mayRename`: is it ours to
  -- obfuscate? Standalone sealing widens the first without touching the second.
  let mayRename := fun n => (findConst? base n).isNone
  let inClosure := if o.standalone then (fun _ => true) else mayRename
  let some ci := findConst? env target | throw s!"no such declaration: {target}"
  let closure := localClosure env inClosure #[target]
  -- The claim is the target's *type*, not its name: the name is obfuscated
  -- like any other, while the definitions the type mentions stay readable.
  let publicSet : NameSet :=
    if o.hideStatement then {} else localClosure env inClosure ci.type.getUsedConstants
  let renameMap <- buildRenameMap o.salt closure publicSet
    (fun n => match findConst? env n with | some (.recInfo _) => true | _ => false)
    mayRename
  let rename := fun (n : Name) => renameMap.getD n n
  let scrubbedTarget := scrubConst rename ci
  let mut out : Array (Name × Json) := #[]
  let mut hidden := 0
  for n in closure.toList do
    let some ci := findConst? env n | throw s!"missing constant {n}"
    -- Recursors are regenerated by the kernel from the inductive declaration,
    -- so shipping ours would only give `replay` a scrubbed copy to reject.
    if ci matches .recInfo _ then continue
    let scrubbed := scrubConst rename ci
    if scrubbed.name != n then hidden := hidden + 1
    out := out.push (scrubbed.name, <- constToJson scrubbed)
  let (root, _, _) := commit (out.map fun (n, j) => (n.toString, j.compress))
  -- Hash the type exactly as it is shipped, universe renumbering included, so
  -- the verifier recomputing it from the artifact gets the same digest.
  let stmtDigest := (<- exprToJson scrubbedTarget.type).compress
  return {
    target := rename target
    statementHash := toHex (sha256s stmtDigest)
    imports
    axioms := (localClosure env (fun _ => true) #[target]).toArray.filter fun n =>
      match findConst? env n with | some (.axiomInfo _) => true | _ => false
    constants := out.qsort (fun a b => a.1.toString < b.1.toString)
    root := toHex root
    -- Both counts range over the declarations actually shipped, so they add
    -- up to the artifact's declaration count.
    hiddenCount := hidden
    publicCount := out.size - hidden }

/-- Serialise a sealed artifact. -/
def Sealed.toJson (s : Sealed) : Json :=
  Json.mkObj [
    ("format", Json.str "zklean-seal/v1"),
    ("hash", Json.str "sha256"),
    ("target", nameToJson s.target),
    ("statement_hash", Json.str s.statementHash),
    ("imports", Json.arr (s.imports.map nameToJson)),
    ("root", Json.str s.root),
    ("constants", Json.arr (s.constants.map fun c => c.2))]

end ZkLean
