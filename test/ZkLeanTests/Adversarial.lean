/-
Fixtures that a verifier must refuse to bless.

Both theorems below are perfectly acceptable to the Lean *kernel*: an axiom is
an axiom, and `sorry` elaborates to `sorryAx`, which is a constant like any
other. Kernel acceptance alone is therefore not enough, which is exactly why
`zklean check` audits the axiom set afterwards and rejects anything outside
`propext` / `Classical.choice` / `Quot.sound`.

If a change ever makes `zklean check` report these as VALID, the tool is broken.
-/
namespace ZkLeanTests.Adversarial

/-- A false assumption, smuggled in as an axiom. -/
axiom cheat : False

/-- "Proved" from a bogus axiom. The kernel accepts this. -/
theorem viaAxiom : (0 : Nat) = 1 := cheat.elim

/-- "Proved" by `sorry`. The kernel accepts this too, via `sorryAx`. -/
theorem viaSorry : (0 : Nat) = 2 := by sorry

/-- An honest theorem in the same module, to show the audit is not just
rejecting everything it sees. -/
theorem honest (n : Nat) : n + 0 = n := Nat.add_zero n

end ZkLeanTests.Adversarial
