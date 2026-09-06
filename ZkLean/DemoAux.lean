/-
A second module in the same development, so the tests have a real cross-module
dependency to point `--include` at.

By default `zklean seal ZkLean.Demo` treats this module as part of the *base*:
its constants keep their names and the artifact reaches them through its import
list. With `--include ZkLean.DemoAux` it becomes part of the sealed development
instead, so its constants are copied into the artifact and obfuscated along with
everything else.
-/
namespace ZkLean.DemoAux

/-- Used by `ZkLean.Demo.double_eq`'s statement. -/
def scale (k n : Nat) : Nat := k * n

theorem scale_one (n : Nat) : scale 1 n = n := Nat.one_mul n

end ZkLean.DemoAux
