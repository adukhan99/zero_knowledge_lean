/-
A small Lean development of the kind you might have mid-research, used both as
the worked example in the README and as the end-to-end test fixture.

Read it as a reference for what survives each stage of the pipeline. Every
theorem here is sealed, obfuscated, and re-checked by the Lean kernel against an
empty environment, and by `nanoda_lib`. The last one is also the honest example
of a limit: it goes through both of those and is still refused by zkPi.

The two sections are not a style preference. They are the boundary of what a
zero-knowledge backend can take today -- see "Reaching a zero-knowledge proof"
in the top-level README.
-/
set_option maxRecDepth 20000

namespace Conjectures

/-! ## Equational results

Structural recursion and equational rewriting. These go all the way through:
Lean kernel, `nanoda_lib`, and zkPi. The `COUNT` figure is zkPi's circuit size
for that theorem, which is the number that decides whether proving it is
affordable. -/

/-- Iterate a function `k` times. -/
def iter (f : Nat -> Nat) : Nat -> Nat -> Nat
  | 0, n => n
  | k + 1, n => iter f k (f n)

/-- The smallest thing worth sealing: true by computation alone.
zkPi circuit size: 1. -/
theorem iter_zero (f : Nat -> Nat) (n : Nat) : iter f 0 n = n := rfl

/-- The recursive step, also definitional. zkPi circuit size: 7. -/
theorem iter_succ (f : Nat -> Nat) (k n : Nat) : iter f (k + 1) n = iter f k (f n) := rfl

/-- Doubling, defined by recursion rather than multiplication. -/
def double : Nat -> Nat
  | 0 => 0
  | n + 1 => double n + 2

/-- A real induction, with arithmetic rewriting. Deliberately proved with
explicit `Nat` lemmas rather than `omega` or `simp`: both of those reach for
`≤`, which is what the second section is about. zkPi circuit size: 51. -/
theorem double_eq_add (n : Nat) : double n = n + n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show double k + 2 = (k + 1) + (k + 1)
    rw [ih, Nat.add_succ, Nat.succ_add, Nat.add_assoc]

/-- A tree, to exercise sealing of an inductive type, its constructors and the
recursor the kernel derives from it. -/
inductive Tree where
  | leaf : Nat -> Tree
  | node : Tree -> Tree -> Tree

/-- Swap every pair of subtrees. -/
def Tree.mirror : Tree -> Tree
  | .leaf n => .leaf n
  | .node l r => .node r.mirror l.mirror

/-- Mirroring is an involution. Structural induction over a user-defined
inductive type. zkPi circuit size: 29. -/
theorem mirror_mirror (t : Tree) : t.mirror.mirror = t := by
  induction t with
  | leaf n => rfl
  | node l r ihl ihr =>
    show Tree.node l.mirror.mirror r.mirror.mirror = _
    rw [ihl, ihr]

/-! ## A bounded search, and the wall it hits

The shape a lot of combinatorial conjectures take: a claim over a finite range,
settled by computation. Lean proves it, the kernel accepts it, and `nanoda_lib`
accepts it. zkPi refuses it.

The reason is not the size of the proof and not the Lean version. Bounded
quantification (`n < bound`) is `Nat.lt`, which is `Nat.le`, which is an
inductive family with a recursive parameter -- and zkPi does not support
recursion on those. It fails loudly rather than silently, which is the right
behaviour, but it does mean the finite-range statements that look most
attractive for zero-knowledge disclosure are the ones currently out of reach. -/

/-- One Collatz step. -/
def step (n : Nat) : Nat := if n % 2 == 0 then n / 2 else 3 * n + 1

/-- Does `n` reach 1 within `fuel` steps? Stops on arrival, since the
trajectory cycles 1 → 4 → 2 → 1 afterwards. -/
def reaches : Nat -> Nat -> Bool
  | _, 1 => true
  | 0, _ => false
  | fuel + 1, n => reaches fuel (step n)

/-- The Collatz conjecture restricted to a finite range. -/
abbrev AllReach (bound fuel : Nat) : Prop :=
  forall n, n < bound -> 0 < n -> reaches fuel n = true

/-- Settled by computation. The proof term is `of_decide_eq_true rfl` -- a
handful of nodes -- but checking it makes the kernel run the entire search.
Small witness, expensive check.

Accepted by the Lean kernel and by `nanoda_lib`; refused by zkPi, for the
reason above. -/
theorem all_reach_32 : AllReach 32 128 := by decide

end Conjectures
