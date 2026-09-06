# `conjectures` — the worked example

A miniature Lean repository standing in for mid-research work. It is the
reference example in the top-level README and the end-to-end test fixture, and
it is a *separate Lake package* on purpose: sealing a repository needs that
repository's modules on the search path, so `zklean` has to run under the source
package's `lake env`. The only honest way to test that is to have a second
package to point at.

```console
$ cd test/fixtures/conjectures
$ lake build
$ lake env ../../../.lake/build/bin/zklean . /tmp/zk-out
```

`Conjectures/Collatz.lean` is deliberately split in two.

**Equational results** (`iter_zero`, `iter_succ`, `double_eq_add`,
`mirror_mirror`) go through every stage: the Lean kernel against an empty
environment, `nanoda_lib`, and zkPi. Their zkPi circuit sizes are 1, 7, 51 and
29 respectively — the number that decides whether proving one is affordable.

**A bounded search** (`all_reach_32`) is the Collatz conjecture over a finite
range, settled by `decide`. It passes the Lean kernel and `nanoda_lib`, and zkPi
refuses it: `n < bound` is `Nat.le`, an inductive family with a recursive
parameter, and zkPi does not support recursion on those. It is kept here
precisely because it fails — a fixture that only ever succeeds tells you nothing
about where the edge is.

The proofs in the first section avoid `omega` and arithmetic `simp` for the same
reason: both reach for `≤`.
