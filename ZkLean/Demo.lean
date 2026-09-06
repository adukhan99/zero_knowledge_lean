/-
A small development to seal. Nothing here is part of the tool; it exists so
`zklean seal ZkLean.Demo` has something to chew on, and so the test script can
check that sealing preserves kernel acceptance.

The shape matters. `Tree`, `Tree.sum`, `Tree.mirror` and `double` are mentioned
by the *statements*, so sealing keeps them readable. `add_comm_nat` and
`double_step` are reached only through the proofs, so sealing replaces them with
opaque names. `scale_one_eq` reaches into a second module, which is what
`--include` controls.
-/
import ZkLean.DemoAux

namespace ZkLean.Demo

open ZkLean.DemoAux

/-- A tiny inductive, to exercise sealing of inductives, constructors and
recursors. It appears in a statement, so it stays public. -/
inductive Tree where
  | leaf : Nat -> Tree
  | node : Tree -> Tree -> Tree

/-- Sum of a tree's leaves. Public: `sum_mirror` mentions it. -/
def Tree.sum : Tree -> Nat
  | .leaf n => n
  | .node l r => l.sum + r.sum

/-- Swap every pair of subtrees. Public. -/
def Tree.mirror : Tree -> Tree
  | .leaf n => .leaf n
  | .node l r => .node r.mirror l.mirror

/-- Hidden: only the proof of `sum_mirror` needs it. -/
private theorem add_comm_nat (a b : Nat) : a + b = b + a := Nat.add_comm a b

/-- Mirroring a tree does not change the sum of its leaves. -/
theorem sum_mirror (t : Tree) : t.mirror.sum = t.sum := by
  induction t with
  | leaf n => rfl
  | node l r ihl ihr =>
    show r.mirror.sum + l.mirror.sum = l.sum + r.sum
    rw [ihl, ihr, add_comm_nat]

/-- Doubling, as a specification the statement can refer to. Public. -/
def double (n : Nat) : Nat := n + n

/-- Hidden helper. -/
private theorem double_step (n : Nat) : n + n = 2 * n := by omega

theorem double_eq (n : Nat) : double n = 2 * n := double_step n

/-- A statement with no interesting dependencies at all. -/
theorem zero_add_self (n : Nat) : 0 + n = n := Nat.zero_add n

/-- Depends on a *different module* of the same development. Sealed by default
against `ZkLean.DemoAux` as base; pulled into the artifact with
`--include ZkLean.DemoAux`. -/
theorem scale_one_eq (n : Nat) : scale 1 n = double n - n := by
  simp [scale, double, Nat.one_mul, Nat.add_sub_cancel]

end ZkLean.Demo
