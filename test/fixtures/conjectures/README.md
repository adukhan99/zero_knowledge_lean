# `conjectures` — an end-to-end fixture

A miniature Lean repository standing in for mid-research work, used by
`test/run.py` to exercise the headline operation:

    cd test/fixtures/conjectures
    lake build
    lake env ../../../.lake/build/bin/zklean . /tmp/zk-out

It is a *separate Lake package* on purpose. Sealing a repository requires that
repository's modules on the search path, so `zklean` has to be run under the
source package's `lake env` — and the only honest way to test that is to have a
second package to point it at.

`all_reach_32` is resolved by `decide`: the proof term is a handful of nodes,
but checking it makes the kernel run the whole search. Small witness, expensive
check — the profile that decides whether a checker can go in a circuit.
