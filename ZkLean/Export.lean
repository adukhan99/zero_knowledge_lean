/-
Emit a sealed artifact in Lean 4's official NDJSON export format (v3.1.0).

Why this exists
---------------
The point of sealing is to end up with something an *independent* checker can
verify. Writing a second Lean kernel is a bad idea -- a kernel that is only
mostly right is an unsound verifier, which is worse than no verifier -- so
instead we speak the format the existing ones already read
(`nanoda_lib`, and anything built on the same formats).

That is also the route to an actual zero-knowledge proof: the program a zkVM
guest runs is one of those checkers, and its private input is this file. See
the roadmap in the README.

Format notes
------------
Names, levels and expressions are interned: each is emitted once, tagged with
the index it defines (`in` / `il` / `ie`), and referred to by index thereafter.
Index 0 is reserved for `Name.anonymous` and `Level.zero`, which are never
emitted. Everything is emitted strictly before its first use, so a checker can
process the stream in one pass without buffering.

Declarations are emitted in dependency order, and an inductive family travels
as one record carrying its types, constructors and recursors together, as the
format requires.
-/
import ZkLean.Check

namespace ZkLean
open Lean

/-- The export format version this emitter targets. -/
def exportFormatVersion : String := "3.1.0"

structure ExportState where
  names  : Std.HashMap Name Nat := ({} : Std.HashMap Name Nat).insert .anonymous 0
  levels : Std.HashMap Level Nat := ({} : Std.HashMap Level Nat).insert .zero 0
  exprs  : Std.HashMap Expr Nat := {}
  /-- Declarations already emitted, so a shared dependency is written once. -/
  done   : NameSet := {}
  lines  : Array Json := #[]

abbrev ExportM := StateM ExportState

private def emit (j : Json) : ExportM Unit :=
  modify fun s => { s with lines := s.lines.push j }

private def obj (fields : List (String × Json)) : Json := Json.mkObj fields

private def num (n : Nat) : Json := Json.num (JsonNumber.fromNat n)

private def idxs (ns : List Nat) : Json := Json.arr (ns.toArray.map num)

/-! ## Interning -/

partial def internName (n : Name) : ExportM Nat := do
  if let some i := (<- get).names[n]? then return i
  match n with
  | .anonymous => return 0
  | .str p s =>
    let pi <- internName p
    let i := (<- get).names.size
    modify fun st => { st with names := st.names.insert n i }
    emit (obj [("str", obj [("pre", num pi), ("str", Json.str s)]), ("in", num i)])
    return i
  | .num p k =>
    let pi <- internName p
    let i := (<- get).names.size
    modify fun st => { st with names := st.names.insert n i }
    emit (obj [("num", obj [("pre", num pi), ("i", num k)]), ("in", num i)])
    return i

mutual

/-- Intern a level, emitting it on first sight. Index 0 is `Level.zero`, which
the format never spells out. -/
partial def internLevel (l : Level) : ExportM Nat := do
  if l matches .zero then return 0
  if let some i := (<- get).levels[l]? then return i
  let fields <- levelFields l
  let i := (<- get).levels.size
  modify fun st => { st with levels := st.levels.insert l i }
  emit (obj (fields ++ [("il", num i)]))
  return i

partial def levelFields : Level -> ExportM (List (String × Json))
  | .zero => return []
  | .succ a => do return [("succ", num (<- internLevel a))]
  | .max a b => do
      let ai <- internLevel a
      let bi <- internLevel b
      return [("max", idxs [ai, bi])]
  | .imax a b => do
      let ai <- internLevel a
      let bi <- internLevel b
      return [("imax", idxs [ai, bi])]
  | .param p => do return [("param", num (<- internName p))]
  -- Refused by the wire decoder long before this point.
  | .mvar _ => return [("unsupported", Json.str "universe metavariable")]

end

private def binderInfoJson : BinderInfo -> Json
  | .default => Json.str "default"
  | .implicit => Json.str "implicit"
  | .strictImplicit => Json.str "strictImplicit"
  | .instImplicit => Json.str "instImplicit"

mutual

/-- Intern an expression, emitting it and its subterms on first sight. -/
partial def internExpr (e : Expr) : ExportM Nat := do
  if let some i := (<- get).exprs[e]? then return i
  let fields <- exprFields e
  let i := (<- get).exprs.size
  modify fun st => { st with exprs := st.exprs.insert e i }
  emit (obj (fields ++ [("ie", num i)]))
  return i

partial def exprFields : Expr -> ExportM (List (String × Json))
  | .bvar k => return [("bvar", num k)]
  | .sort l => do return [("sort", num (<- internLevel l))]
  | .const n us => do
      let ni <- internName n
      let uis <- us.mapM internLevel
      return [("const", obj [("name", num ni), ("us", idxs uis)])]
  | .app f a => do
      let fi <- internExpr f
      let ai <- internExpr a
      return [("app", obj [("fn", num fi), ("arg", num ai)])]
  | .lam n t b bi => do
      let ni <- internName n
      let ti <- internExpr t
      let bd <- internExpr b
      return [("lam", obj [("name", num ni), ("type", num ti), ("body", num bd),
                           ("binderInfo", binderInfoJson bi)])]
  | .forallE n t b bi => do
      let ni <- internName n
      let ti <- internExpr t
      let bd <- internExpr b
      return [("forallE", obj [("name", num ni), ("type", num ti), ("body", num bd),
                               ("binderInfo", binderInfoJson bi)])]
  | .letE n t v b nd => do
      let ni <- internName n
      let ti <- internExpr t
      let vi <- internExpr v
      let bd <- internExpr b
      return [("letE", obj [("name", num ni), ("type", num ti), ("value", num vi),
                            ("body", num bd), ("nondep", Json.bool nd)])]
  | .proj st k s => do
      let si <- internName st
      let sti <- internExpr s
      return [("proj", obj [("typeName", num si), ("idx", num k), ("struct", num sti)])]
  | .lit (.natVal k) => return [("natVal", Json.str (toString k))]
  | .lit (.strVal s) => return [("strVal", Json.str s)]
  -- Sealing strips `mdata`, and the wire decoder refuses open terms, so
  -- neither of these can reach a sealed artifact.
  | .mdata _ inner => do return [("mdataStripped", num (<- internExpr inner))]
  | .fvar _ | .mvar _ => return [("unsupported", Json.str "open term")]

end

/-! ## Declarations -/

private def cvFields (v : ConstantVal) : ExportM (List (String × Json)) := do
  let ni <- internName v.name
  let lps <- v.levelParams.mapM internName
  let ti <- internExpr v.type
  return [("name", num ni), ("levelParams", idxs lps), ("type", num ti)]

private def hintsJson : ReducibilityHints -> Json
  | .opaque => Json.str "opaque"
  | .abbrev => Json.str "abbrev"
  | .regular h => Json.mkObj [("regular", num h.toNat)]

private def inductiveValJson (v : InductiveVal) : ExportM Json := do
  let base <- cvFields v.toConstantVal
  let all <- v.all.mapM internName
  let ctors <- v.ctors.mapM internName
  return obj (base ++ [
    ("numParams", num v.numParams), ("numIndices", num v.numIndices),
    ("all", idxs all), ("ctors", idxs ctors), ("numNested", num v.numNested),
    ("isRec", Json.bool v.isRec), ("isUnsafe", Json.bool v.isUnsafe),
    ("isReflexive", Json.bool v.isReflexive)])

private def ctorValJson (v : ConstructorVal) : ExportM Json := do
  let base <- cvFields v.toConstantVal
  let ind <- internName v.induct
  return obj (base ++ [
    ("induct", num ind), ("cidx", num v.cidx), ("numParams", num v.numParams),
    ("numFields", num v.numFields), ("isUnsafe", Json.bool v.isUnsafe)])

private def recValJson (v : RecursorVal) : ExportM Json := do
  let base <- cvFields v.toConstantVal
  let all <- v.all.mapM internName
  let rules <- v.rules.mapM fun r => do
    let ci <- internName r.ctor
    let rhs <- internExpr r.rhs
    -- `nfields`, not `nFields`: the published spec has a typo here, and
    -- real `lean4export` output and `nanoda_lib` both use the lowercase form.
    return obj [("ctor", num ci), ("nfields", num r.nfields), ("rhs", num rhs)]
  return obj (base ++ [
    ("all", idxs all), ("numParams", num v.numParams), ("numIndices", num v.numIndices),
    ("numMotives", num v.numMotives), ("numMinors", num v.numMinors),
    ("rules", Json.arr rules.toArray), ("k", Json.bool v.k),
    ("isUnsafe", Json.bool v.isUnsafe)])

/-- Recursor names grouped by the inductive family they belong to.

Lean names a plain inductive's recursor `<T>.rec`, but a *mutual* or *nested*
block gets `<T>.rec_1`, `<T>.rec_2`, ... instead. Constructing the names by hand
is therefore wrong, and wrong in a way that only shows up on nested inductives
(`omega` proofs drag in `Lean.Syntax`, which is one). `RecursorVal.all` is
authoritative, so group by it and scan once. -/
def recursorsByFamily (env : Environment) : Std.HashMap Name (Array Name) :=
  let m := env.constants.fold (init := ({} : Std.HashMap Name (Array Name)))
    fun acc n ci =>
      match ci with
      | .recInfo v =>
        match v.all.head? with
        | some head => acc.insert head ((acc.getD head #[]).push n)
        | none => acc
      | _ => acc
  -- `fold` order over the constant map is not specified; sort for determinism.
  m.fold (init := {}) fun acc k v => acc.insert k (v.qsort (fun a b => a.toString < b.toString))

/-- Emit `n` and everything it depends on, dependencies first.

An inductive family is emitted as a single record: the format groups its types,
constructors and recursors together, and a checker needs the whole block to
derive the recursors for itself. -/
partial def emitConst (env : Environment) (recMap : Std.HashMap Name (Array Name))
    (n : Name) : ExportM Unit := do
  if (<- get).done.contains n then return
  let some ci := findConst? env n | return
  -- Constructors and recursors are reached through their inductive block.
  match ci with
  | .ctorInfo v => emitConst env recMap v.induct; return
  | .recInfo v =>
    match v.all.head? with
    | some ind => emitConst env recMap ind; return
    | none => return
  | _ => pure ()
  -- Claim the name before recursing, so a cycle cannot loop forever. Mutual
  -- blocks are genuinely cyclic through their `all` lists.
  modify fun s => { s with done := s.done.insert n }
  match ci with
  | .inductInfo v =>
    let family := v.all
    let recNames := (recMap.getD (family.headD n) #[]).toList
    let members := family ++ v.ctors ++ recNames
    for m in members do
      modify fun s => { s with done := s.done.insert m }
    -- Dependencies of the whole block, minus the block itself.
    for m in members do
      if let some mi := findConst? env m then
        for d in mi.getUsedConstantsAsSet.toList do
          unless members.contains d do emitConst env recMap d
    let types <- family.filterMapM fun m => do
      match findConst? env m with
      | some (.inductInfo w) => return some (<- inductiveValJson w)
      | _ => return none
    let ctors <- v.all.flatMapM fun m => do
      match findConst? env m with
      | some (.inductInfo w) => w.ctors.filterMapM fun c => do
          match findConst? env c with
          | some (.ctorInfo cw) => return some (<- ctorValJson cw)
          | _ => return none
      | _ => return []
    let recs <- recNames.filterMapM fun r => do
      match findConst? env r with
      | some (.recInfo rw) => return some (<- recValJson rw)
      | _ => return none
    emit (obj [("inductive", obj [("types", Json.arr types.toArray),
                                  ("ctors", Json.arr ctors.toArray),
                                  ("recs", Json.arr recs.toArray)])])
  | _ =>
    for d in ci.getUsedConstantsAsSet.toList do
      emitConst env recMap d
    match ci with
    | .axiomInfo v =>
      emit (obj [("axiom", obj ((<- cvFields v.toConstantVal) ++
        [("isUnsafe", Json.bool v.isUnsafe)]))])
    | .thmInfo v =>
      let val <- internExpr v.value
      let all <- v.all.mapM internName
      emit (obj [("thm", obj ((<- cvFields v.toConstantVal) ++
        [("value", num val), ("all", idxs all)]))])
    | .defnInfo v =>
      let val <- internExpr v.value
      let all <- v.all.mapM internName
      let safety := match v.safety with
        | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"
      emit (obj [("def", obj ((<- cvFields v.toConstantVal) ++
        [("value", num val), ("hints", hintsJson v.hints),
         ("safety", Json.str safety), ("all", idxs all)]))])
    | .opaqueInfo v =>
      let val <- internExpr v.value
      let all <- v.all.mapM internName
      emit (obj [("opaque", obj ((<- cvFields v.toConstantVal) ++
        [("value", num val), ("isUnsafe", Json.bool v.isUnsafe), ("all", idxs all)]))])
    | .quotInfo v =>
      let kind := match v.kind with
        | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
      emit (obj [("quot", obj ((<- cvFields v.toConstantVal) ++
        [("kind", Json.str kind)]))])
    | _ => pure ()

/-- The metadata record every export file opens with. -/
def metaLine : Json :=
  Json.mkObj [("meta", Json.mkObj [
    ("exporter", Json.mkObj [("name", Json.str "zklean"), ("version", Json.str "0.3.0")]),
    ("lean", Json.mkObj [("githash", Json.str Lean.githash),
                         ("version", Json.str Lean.versionString)]),
    ("format", Json.mkObj [("version", Json.str exportFormatVersion)])])]

/-- Render `roots` and their dependencies as NDJSON. -/
def exportNdjson (env : Environment) (roots : Array Name) : String :=
  let recMap := recursorsByFamily env
  let st := (roots.forM (emitConst env recMap)).run { } |>.2
  String.intercalate "\n" ((#[metaLine] ++ st.lines).toList.map Json.compress) ++ "\n"


/-! ## The legacy line-based export format

Lean's original export format, still what some external checkers read --
notably [zkPi](https://github.com/emlaufer/zkpi), which pins `v4.8.0-rc1`.

Emitting it is pure interoperability: the format is Lean's, not any consumer's,
and a file format is not a derivative work of the programs that read it. So
this needs no permission from anyone, and it deliberately takes on none of any
consumer's guarantees -- it produces a file, and whatever a checker concludes
from that file is between the user and that checker.

The translation runs over the NDJSON lines rather than re-walking the
environment, so the two formats cannot drift apart: every index, and the order
they are defined in, is by construction the same.

Differences the format forces:
* theorems are emitted as `#DEF`; there is no `#THM`;
* recursors are dropped, because the format has no way to spell them and every
  consumer derives them from `#IND` itself;
* `#QUOT` takes no arguments and declares the whole quotient package at once;
* reducibility hints are dropped, being a performance annotation only.
-/

private def hexDigitsUpper : Array Char :=
  #['0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F']

private def hexByte (b : UInt8) : String :=
  s!"{hexDigitsUpper[b.toNat / 16]!}{hexDigitsUpper[b.toNat % 16]!}"

private def binderTag : Nat -> String
  | 0 => "#BD" | 1 => "#BI" | 2 => "#BS" | _ => "#BC"

private def jNat (j : Json) : Except String Nat := do
  match j with
  | .num n => return n.mantissa.natAbs
  | .str s => match s.toNat? with
              | some k => return k
              | none => throw s!"legacy: expected a decimal number, got {s}"
  | _ => throw "legacy: expected a number"

private def jNats (j : Json) : Except String (List Nat) :=
  return (<- (<- j.getArr?).mapM jNat).toList

/-- Space-separated, empty for an empty list.

The reference exporter interpolates this after a literal space, so an empty
list leaves a trailing space on the line. That is reproduced deliberately: the
goal is byte-identical output, and guessing that a consumer's parser tolerates
the difference is not worth the risk. -/
private def seqStr (ns : List Nat) : String := String.intercalate " " (ns.map toString)

/-- Translate one NDJSON record. `none` means "emits nothing in this format". -/
private def legacyLine (j : Json) (quotDone : Bool) : Except String (Option String × Bool) := do
  let keep (s : String) : Except String (Option String × Bool) := return (some s, quotDone)
  if (j.getObjVal? "meta").isOk then return (none, quotDone)
  -- Primitives carry the index they define.
  if let .ok idx := j.getObjVal? "in" then
    let i <- jNat idx
    if let .ok o := j.getObjVal? "str" then
      keep s!"{i} #NS {<- jNat (<- o.getObjVal? "pre")} {<- (<- o.getObjVal? "str").getStr?}"
    else
      let o <- j.getObjVal? "num"
      keep s!"{i} #NI {<- jNat (<- o.getObjVal? "pre")} {<- jNat (<- o.getObjVal? "i")}"
  else if let .ok idx := j.getObjVal? "il" then
    let i <- jNat idx
    if let .ok a := j.getObjVal? "succ" then keep s!"{i} #US {<- jNat a}"
    else if let .ok a := j.getObjVal? "max" then
      match <- jNats a with
      | [x, y] => keep s!"{i} #UM {x} {y}"
      | _ => throw "legacy: malformed max level"
    else if let .ok a := j.getObjVal? "imax" then
      match <- jNats a with
      | [x, y] => keep s!"{i} #UIM {x} {y}"
      | _ => throw "legacy: malformed imax level"
    else if let .ok a := j.getObjVal? "param" then keep s!"{i} #UP {<- jNat a}"
    else throw "legacy: unrecognised level record"
  else if let .ok idx := j.getObjVal? "ie" then
    let i <- jNat idx
    if let .ok a := j.getObjVal? "bvar" then keep s!"{i} #EV {<- jNat a}"
    else if let .ok a := j.getObjVal? "sort" then keep s!"{i} #ES {<- jNat a}"
    else if let .ok o := j.getObjVal? "const" then
      keep s!"{i} #EC {<- jNat (<- o.getObjVal? "name")} {seqStr (<- jNats (<- o.getObjVal? "us"))}"
    else if let .ok o := j.getObjVal? "app" then
      keep s!"{i} #EA {<- jNat (<- o.getObjVal? "fn")} {<- jNat (<- o.getObjVal? "arg")}"
    else if let .ok o := j.getObjVal? "lam" then
      keep s!"{i} #EL {binderTag (<- binderIdx o)} {<- jNat (<- o.getObjVal? "name")} \
{<- jNat (<- o.getObjVal? "type")} {<- jNat (<- o.getObjVal? "body")}"
    else if let .ok o := j.getObjVal? "forallE" then
      keep s!"{i} #EP {binderTag (<- binderIdx o)} {<- jNat (<- o.getObjVal? "name")} \
{<- jNat (<- o.getObjVal? "type")} {<- jNat (<- o.getObjVal? "body")}"
    else if let .ok o := j.getObjVal? "letE" then
      keep s!"{i} #EZ {<- jNat (<- o.getObjVal? "name")} {<- jNat (<- o.getObjVal? "type")} \
{<- jNat (<- o.getObjVal? "value")} {<- jNat (<- o.getObjVal? "body")}"
    else if let .ok o := j.getObjVal? "proj" then
      keep s!"{i} #EJ {<- jNat (<- o.getObjVal? "typeName")} {<- jNat (<- o.getObjVal? "idx")} \
{<- jNat (<- o.getObjVal? "struct")}"
    else if let .ok a := j.getObjVal? "natVal" then keep s!"{i} #ELN {<- jNat a}"
    else if let .ok a := j.getObjVal? "strVal" then
      keep s!"{i} #ELS {String.intercalate " " ((<- a.getStr?).toUTF8.toList.map hexByte)}"
    else throw "legacy: unrecognised expression record"
  -- Declarations carry no index.
  else if let .ok o := j.getObjVal? "axiom" then
    keep s!"#AX {<- jNat (<- o.getObjVal? "name")} {<- jNat (<- o.getObjVal? "type")} \
{seqStr (<- jNats (<- o.getObjVal? "levelParams"))}"
  else if let some o := valued j then
    -- Definitions, theorems and opaques all become `#DEF`; the reference
    -- exporter does the same, and the format has no other spelling for them.
    keep s!"#DEF {<- jNat (<- o.getObjVal? "name")} {<- jNat (<- o.getObjVal? "type")} \
{<- jNat (<- o.getObjVal? "value")} {seqStr (<- jNats (<- o.getObjVal? "levelParams"))}"
  else if (j.getObjVal? "quot").isOk then
    -- Lean 4 has four quotient constants; this format has one argument-less
    -- record that declares the whole package, so emit it once.
    if quotDone then return (none, true) else return (some "#QUOT", true)
  else if let .ok o := j.getObjVal? "inductive" then
    -- One record per type, as the reference exporter emits: it walks constants
    -- one at a time, so a mutual block simply produces consecutive records.
    let ctorArr <- (<- o.getObjVal? "ctors").getArr?
    let mut ctorType : Std.HashMap Nat Nat := {}
    for c in ctorArr do
      ctorType := ctorType.insert (<- jNat (<- c.getObjVal? "name")) (<- jNat (<- c.getObjVal? "type"))
    let mut out : Array String := #[]
    for t in <- (<- o.getObjVal? "types").getArr? do
      let ctors <- jNats (<- t.getObjVal? "ctors")
      let intros <- ctors.flatMapM fun c => do
        match ctorType[c]? with
        | some ty => return [c, ty]
        | none => throw s!"legacy: constructor {c} missing from its inductive block"
      out := out.push s!"#IND {<- jNat (<- t.getObjVal? "numParams")} \
{<- jNat (<- t.getObjVal? "name")} {<- jNat (<- t.getObjVal? "type")} {ctors.length} \
{seqStr intros} {seqStr (<- jNats (<- t.getObjVal? "levelParams"))}"
    return (some (String.intercalate "\n" out.toList), quotDone)
  else throw "legacy: unrecognised record"
where
  /-- The body of whichever value-carrying declaration this record is. -/
  valued (j : Json) : Option Json :=
    ["def", "thm", "opaque"].findSome? fun k => (j.getObjVal? k).toOption

  binderIdx (o : Json) : Except String Nat := do
    match <- (<- o.getObjVal? "binderInfo").getStr? with
    | "default" => return 0
    | "implicit" => return 1
    | "strictImplicit" => return 2
    | "instImplicit" => return 3
    | s => throw s!"legacy: unknown binder info {s}"

/-- Render `roots` in the legacy line-based export format. -/
def exportLegacy (env : Environment) (roots : Array Name) : Except String String := do
  let recMap := recursorsByFamily env
  let st := (roots.forM (emitConst env recMap)).run { } |>.2
  let mut out : Array String := #[]
  let mut quotDone := false
  for line in st.lines do
    let (rendered, q) <- legacyLine line quotDone
    quotDone := q
    if let some text := rendered then out := out.push text
  return String.intercalate "\n" out.toList ++ "\n"

end ZkLean
