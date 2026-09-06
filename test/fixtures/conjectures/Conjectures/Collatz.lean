/-
A stand-in for mid-research work: a conjecture stated over a finite range and
resolved by computation. This is the shape a lot of Erdos-style combinatorial
results actually have, and it is the tractable case for putting a proof checker
in a circuit -- the proof *term* is tiny, even though checking it is not.
-/
set_option maxRecDepth 20000

namespace Conjectures

/-- One Collatz step. -/
def step (n : Nat) : Nat := if n % 2 == 0 then n / 2 else 3 * n + 1

/-- Does `n` reach 1 within `fuel` steps? Stops on arrival, because the
trajectory cycles 1 -> 4 -> 2 -> 1 afterwards. -/
def reaches : Nat -> Nat -> Bool
  | _, 1 => true
  | 0, _ => false
  | fuel + 1, n => reaches fuel (step n)

/-- The conjecture restricted to a finite range: every positive start below
`bound` reaches 1 within `fuel` steps. This is the public claim. -/
abbrev AllReach (bound fuel : Nat) : Prop :=
  forall n, n < bound -> 0 < n -> reaches fuel n = true

/-- Resolved by computation. The proof term is `of_decide_eq_true rfl` -- a
handful of nodes -- but checking it makes the kernel run the entire search.
Small witness, expensive check. -/
theorem all_reach_32 : AllReach 32 128 := by decide

/-- A second, independent result, so the repository has more than one leaf. -/
theorem step_double (n : Nat) : step (2 * n) = n := by
  simp [step, Nat.mul_mod_right]

end Conjectures
