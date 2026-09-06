/-
Canonical JSON codec for Lean kernel declarations (`Name`, `Level`, `Expr`,
`ConstantInfo`).

The encoding is deliberately positional and terse: every node is a JSON array
whose head is a one-character tag. This keeps sealed artifacts small and, more
importantly, canonical — two structurally equal declarations always encode to
the same bytes, which is what makes the Merkle commitment well defined.

`Expr.mdata` is dropped (it carries elaborator annotations that the kernel
ignores) and `Expr.fvar` / `Expr.mvar` / `Level.mvar` are rejected: a closed
kernel declaration contains none of them, and accepting them would let an
artifact smuggle in an unchecked hole.
-/
import Lean
import ZkLean.Sha256

namespace ZkLean
open Lean

abbrev Res := Except String

private def tag (t : String) (args : Array Json) : Json := Json.arr (#[Json.str t] ++ args)

private def nat (n : Nat) : Json := Json.str (toString n)

private def getNat (j : Json) : Res Nat := do
  let s ← j.getStr?
  match s.toNat? with
  | some n => return n
  | none => throw s!"expected a decimal natural, got {s}"

private def field (j : Json) (i : Nat) : Res Json := do
  let a ← j.getArr?
  if h : i < a.size then return a[i] else throw s!"wire: missing field {i}"

private def tagOf (j : Json) : Res String := do (← field j 0).getStr?

/-! ## `Name` -/

/-- A name encodes as its component list, e.g. `Nat.succ ↦ ["Nat","succ"]`;
numeric components become one-element objects to keep them distinguishable. -/
def nameToJson (n : Name) : Json :=
  let rec go : Name → Array Json
    | .anonymous => #[]
    | .str p s => (go p).push (Json.str s)
    | .num p i => (go p).push (Json.mkObj [("i", nat i)])
  Json.arr (go n)

def nameOfJson (j : Json) : Res Name := do
  let parts ← j.getArr?
  parts.foldlM (init := Name.anonymous) fun acc p =>
    match p with
    | .str s => return acc.str s
    | .obj _ => return acc.num (← getNat (← p.getObjVal? "i"))
    | _ => throw "wire: bad name component"

/-! ## `Level` -/

partial def levelToJson : Level → Res Json
  | .zero => return tag "z" #[]
  | .succ l => return tag "s" #[← levelToJson l]
  | .max a b => return tag "m" #[← levelToJson a, ← levelToJson b]
  | .imax a b => return tag "i" #[← levelToJson a, ← levelToJson b]
  | .param n => return tag "p" #[nameToJson n]
  | .mvar _ => throw "wire: universe metavariable in a sealed declaration"

partial def levelOfJson (j : Json) : Res Level := do
  match ← tagOf j with
  | "z" => return .zero
  | "s" => return .succ (← levelOfJson (← field j 1))
  | "m" => return .max (← levelOfJson (← field j 1)) (← levelOfJson (← field j 2))
  | "i" => return .imax (← levelOfJson (← field j 1)) (← levelOfJson (← field j 2))
  | "p" => return .param (← nameOfJson (← field j 1))
  | t => throw s!"wire: unknown level tag {t}"

private def levelsToJson (ls : List Level) : Res Json :=
  return Json.arr (← (ls.toArray.mapM levelToJson))

private def levelsOfJson (j : Json) : Res (List Level) :=
  return (← (← j.getArr?).mapM levelOfJson).toList

/-! ## `Expr` -/

private def biToJson : BinderInfo → Json
  | .default => nat 0
  | .implicit => nat 1
  | .strictImplicit => nat 2
  | .instImplicit => nat 3

private def biOfJson (j : Json) : Res BinderInfo := do
  match ← getNat j with
  | 0 => return .default
  | 1 => return .implicit
  | 2 => return .strictImplicit
  | 3 => return .instImplicit
  | n => throw s!"wire: bad binder info {n}"

/-- Binder names are cosmetic; sealing replaces them all with a single
placeholder, so they are not carried on the wire at all. -/
private def binderName : Name := `x

partial def exprToJson : Expr → Res Json
  | .bvar i => return tag "b" #[nat i]
  | .sort l => return tag "s" #[← levelToJson l]
  | .const n ls => return tag "c" #[nameToJson n, ← levelsToJson ls]
  | .app f a => return tag "a" #[← exprToJson f, ← exprToJson a]
  | .lam _ t b bi => return tag "l" #[← exprToJson t, ← exprToJson b, biToJson bi]
  | .forallE _ t b bi => return tag "f" #[← exprToJson t, ← exprToJson b, biToJson bi]
  | .letE _ t v b nd => return tag "e" #[← exprToJson t, ← exprToJson v, ← exprToJson b, Json.bool nd]
  | .lit (.natVal n) => return tag "n" #[nat n]
  | .lit (.strVal s) => return tag "t" #[Json.str s]
  | .proj s i e => return tag "j" #[nameToJson s, nat i, ← exprToJson e]
  | .mdata _ e => exprToJson e
  | .fvar _ => throw "wire: free variable in a sealed declaration"
  | .mvar _ => throw "wire: metavariable in a sealed declaration"

partial def exprOfJson (j : Json) : Res Expr := do
  match ← tagOf j with
  | "b" => return .bvar (← getNat (← field j 1))
  | "s" => return .sort (← levelOfJson (← field j 1))
  | "c" => return .const (← nameOfJson (← field j 1)) (← levelsOfJson (← field j 2))
  | "a" => return .app (← exprOfJson (← field j 1)) (← exprOfJson (← field j 2))
  | "l" => return .lam binderName (← exprOfJson (← field j 1)) (← exprOfJson (← field j 2))
             (← biOfJson (← field j 3))
  | "f" => return .forallE binderName (← exprOfJson (← field j 1)) (← exprOfJson (← field j 2))
             (← biOfJson (← field j 3))
  | "e" => return .letE binderName (← exprOfJson (← field j 1)) (← exprOfJson (← field j 2))
             (← exprOfJson (← field j 3)) (← (← field j 4).getBool?)
  | "n" => return .lit (.natVal (← getNat (← field j 1)))
  | "t" => return .lit (.strVal (← (← field j 1).getStr?))
  | "j" => return .proj (← nameOfJson (← field j 1)) (← getNat (← field j 2))
             (← exprOfJson (← field j 3))
  | t => throw s!"wire: unknown expression tag {t}"

/-! ## `ConstantInfo` -/

private def namesToJson (ns : List Name) : Json := Json.arr (ns.toArray.map nameToJson)

private def namesOfJson (j : Json) : Res (List Name) :=
  return (← (← j.getArr?).mapM nameOfJson).toList

private def hintsToJson : ReducibilityHints → Json
  | .opaque => nat 0
  | .abbrev => nat 1
  | .regular h => Json.arr #[nat 2, nat h.toNat]

private def hintsOfJson (j : Json) : Res ReducibilityHints := do
  match j with
  | .arr _ => return .regular (UInt32.ofNat (← getNat (← field j 1)))
  | _ => match ← getNat j with
         | 0 => return .opaque
         | 1 => return .abbrev
         | n => throw s!"wire: bad reducibility hint {n}"

private def cvToJson (v : ConstantVal) : Res (Array Json) :=
  return #[nameToJson v.name, namesToJson v.levelParams, ← exprToJson v.type]

private def cvOfJson (j : Json) (o : Nat) : Res ConstantVal := do
  let name ← nameOfJson (← field j o)
  let levelParams ← namesOfJson (← field j (o + 1))
  let type ← exprOfJson (← field j (o + 2))
  return { name, levelParams, type }

/-- Encode a constant. Definitions are always emitted as `safe`; `unsafe` and
`partial` constants are refused outright, since the kernel does not check them. -/
def constToJson : ConstantInfo → Res Json
  | .axiomInfo v => do
      if v.isUnsafe then throw s!"seal: refusing unsafe axiom {v.name}"
      return tag "ax" (← cvToJson v.toConstantVal)
  | .thmInfo v => do
      return tag "th" ((← cvToJson v.toConstantVal) ++ #[← exprToJson v.value, namesToJson v.all])
  | .defnInfo v => do
      if v.safety != .safe then throw s!"seal: refusing non-safe definition {v.name}"
      return tag "df" ((← cvToJson v.toConstantVal) ++
        #[← exprToJson v.value, hintsToJson v.hints, namesToJson v.all])
  | .opaqueInfo v => do
      if v.isUnsafe then throw s!"seal: refusing unsafe opaque {v.name}"
      return tag "op" ((← cvToJson v.toConstantVal) ++ #[← exprToJson v.value, namesToJson v.all])
  | .inductInfo v => do
      if v.isUnsafe then throw s!"seal: refusing unsafe inductive {v.name}"
      return tag "in" ((← cvToJson v.toConstantVal) ++
        #[nat v.numParams, nat v.numIndices, namesToJson v.all, namesToJson v.ctors,
          nat v.numNested, Json.bool v.isRec, Json.bool v.isReflexive])
  | .ctorInfo v => do
      if v.isUnsafe then throw s!"seal: refusing unsafe constructor {v.name}"
      return tag "ct" ((← cvToJson v.toConstantVal) ++
        #[nameToJson v.induct, nat v.cidx, nat v.numParams, nat v.numFields])
  | .recInfo v => do
      if v.isUnsafe then throw s!"seal: refusing unsafe recursor {v.name}"
      let rules ← v.rules.toArray.mapM fun r =>
        return Json.arr #[nameToJson r.ctor, nat r.nfields, ← exprToJson r.rhs]
      return tag "rc" ((← cvToJson v.toConstantVal) ++
        #[namesToJson v.all, nat v.numParams, nat v.numIndices, nat v.numMotives,
          nat v.numMinors, Json.arr rules, Json.bool v.k])
  | .quotInfo v => do
      let k : Nat := match v.kind with
        | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
      return tag "qt" ((← cvToJson v.toConstantVal) ++ #[nat k])

def constOfJson (j : Json) : Res ConstantInfo := do
  let cv ← cvOfJson j 1
  let e (i : Nat) : Res Expr := do exprOfJson (← field j i)
  let n (i : Nat) : Res Nat := do getNat (← field j i)
  let nm (i : Nat) : Res Name := do nameOfJson (← field j i)
  let ns (i : Nat) : Res (List Name) := do namesOfJson (← field j i)
  let b (i : Nat) : Res Bool := do (← field j i).getBool?
  match ← tagOf j with
  | "ax" =>
    return .axiomInfo { toConstantVal := cv, isUnsafe := false }
  | "th" =>
    let value ← e 4; let all ← ns 5
    return .thmInfo { toConstantVal := cv, value, all }
  | "df" =>
    let value ← e 4; let hints ← hintsOfJson (← field j 5); let all ← ns 6
    return .defnInfo { toConstantVal := cv, value, hints, safety := .safe, all }
  | "op" =>
    let value ← e 4; let all ← ns 5
    return .opaqueInfo { toConstantVal := cv, value, isUnsafe := false, all }
  | "in" =>
    let numParams ← n 4; let numIndices ← n 5; let all ← ns 6; let ctors ← ns 7
    let numNested ← n 8; let isRec ← b 9; let isReflexive ← b 10
    return .inductInfo { toConstantVal := cv, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe := false, isReflexive }
  | "ct" =>
    let induct ← nm 4; let cidx ← n 5; let numParams ← n 6; let numFields ← n 7
    return .ctorInfo { toConstantVal := cv, induct, cidx, numParams, numFields, isUnsafe := false }
  | "rc" =>
    let all ← ns 4; let numParams ← n 5; let numIndices ← n 6
    let numMotives ← n 7; let numMinors ← n 8; let k ← b 10
    let rules ← (← (← field j 9).getArr?).mapM fun r => do
      let ctor ← nameOfJson (← field r 0)
      let nfields ← getNat (← field r 1)
      let rhs ← exprOfJson (← field r 2)
      return ({ ctor, nfields, rhs } : RecursorRule)
    return .recInfo { toConstantVal := cv, all, numParams, numIndices, numMotives, numMinors, rules := rules.toList, k, isUnsafe := false }
  | "qt" =>
    let kind ← match ← n 4 with
      | 0 => pure QuotKind.type
      | 1 => pure .ctor
      | 2 => pure .lift
      | 3 => pure .ind
      | k => throw s!"wire: bad quotient kind {k}"
    return .quotInfo { toConstantVal := cv, kind }
  | t => throw s!"wire: unknown constant tag {t}"

/-- The canonical bytes a constant is committed to: its JSON encoding, compacted. -/
def constDigest (c : ConstantInfo) : Res String :=
  return (← constToJson c).compress

end ZkLean
