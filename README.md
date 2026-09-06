# zklean

Seal a Lean 4 proof into an artifact that is **totally obfuscated but still
kernel-checkable**. A recipient can confirm *"this theorem is proved, from the
standard axioms, with no `sorry`"* without receiving your source, your tactics,
your names, or any other theorem in your development.

```console
$ zklean seal ZkLean.Demo ZkLean.Demo.sum_mirror
salt        : 0f3c…  (keep this to re-derive the mapping)
ZkLean.Demo.sum_mirror
  sealed as : _zkb500dbb9abfb8676
  hidden    : 2 declarations   public: 12
  artifact  : zkl/_zkb500dbb9abfb8676.zkl.json

$ zklean check zkl/_zkb500dbb9abfb8676.zkl.json
VALID    zkl/_zkb500dbb9abfb8676.zkl.json
  target      : _zkb500dbb9abfb8676
  statement   : ∀ (x : ZkLean.Demo.Tree),
                  Eq (ZkLean.Demo.Tree.sum (ZkLean.Demo.Tree.mirror x))
                     (ZkLean.Demo.Tree.sum x)
  declarations: 14 (all accepted by the kernel)
  axioms      : none
```

The statement is legible. The proof is a name-stripped elaborated term. Nothing
else from the repository is in the file.

## What this is, precisely

**This is obfuscation with verifiability. It is not yet a zero-knowledge
proof.** The distinction matters, so it is worth being blunt about it.

The artifact *contains* the proof term — that is how a kernel can check it.
What sealing removes is everything around it: source text, comments,
docstrings, tactic scripts, file structure, every name your development
introduced, every binder name, every universe parameter name, and every
declaration the target does not depend on. What survives is a fully explicit
term that no human will read for pleasure, but that a kernel accepts or rejects
with no ambiguity.

A genuine zero-knowledge proof — where the verifier learns *nothing* beyond
"a proof exists" — needs Lean's type checker to run inside a circuit. See
[the roadmap](#roadmap-to-an-actual-zero-knowledge-proof); the pieces that
project depends on are built and tested here, and the remaining gap is named
precisely rather than papered over.

Three things worth knowing before relying on any of this:

- **Resolution is asymmetric.** You can attest *"I hold a proof of P"* or
  *"I hold a proof of ¬P"*. You cannot attest *"P is undecided"*, and the
  absence of an artifact is evidence of nothing.
- **Publishing an attestation leaks the most valuable bit.** "Here is a proof
  that P holds" tells the world P is resolved and in which direction. Mid
  research that is often exactly what invites a race. Use `--hide-statement`
  and publish only the Merkle root when you want priority without disclosure,
  and open it later.
- **A `VALID` verdict is about the kernel, not about you.** It says the term
  type-checks and rests only on the standard axioms. It says nothing about
  whether the statement is the one you meant to prove.

## Soundness

`zklean check` decides nothing itself. It decodes the artifact and hands every
declaration to `Lean.Environment.replay`, which submits each one to the kernel
at trust level 0 — the same code path `lean4checker` uses. The trusted base is
the Lean kernel, exactly as when you run `lake build` on the original source.

Kernel acceptance alone is *not* sufficient, and the tool does not pretend
otherwise. An artifact is free to declare `axiom cheat : False` and prove
anything from it, and the kernel will accept that happily. So after replay,
`check` walks the target's transitive dependencies and reports every axiom it
finds, rejecting anything outside Lean's standard three (`propext`,
`Classical.choice`, `Quot.sound`). `sorry` shows up here as `sorryAx` and is
called out by name.

Four independent things must hold before an artifact is called `VALID`:

| check | catches |
| --- | --- |
| Merkle root recomputed from the declarations | edited declarations |
| kernel replay of every declaration | ill-typed or incoherent proof terms |
| statement digest recomputed from the target's type | a proof relabelled with a different claim |
| axiom audit over the replayed environment | smuggled axioms, `sorry` |

The wire decoder also refuses open terms (`fvar`/`mvar`), `unsafe` and
`partial` declarations, duplicate declarations, quotient constants, and any
attempt to redefine an imported constant.

The artifact's import list is attacker-controlled, so it is worth saying what
that does *not* buy an attacker: the axiom audit walks the target's whole
transitive closure, base environment included, so an axiom reached through an
imported module is reported exactly like one declared in the artifact. (An
attacker who can place a malicious `.olean` on your `LEAN_PATH` has already won,
but that is true of `lake build` too.)

The test suite builds artifacts that pass the first and third checks by
construction — it recomputes the commitment and the statement digest honestly
after tampering — so that the rejection it then requires can only be coming
from the kernel.

## What is hidden, and what is not

By default the *statement* stays readable and the *proof* does not. Concretely,
the constants reachable from the target's type keep their names, because you
cannot understand a claim about `Tree.mirror` without knowing what `Tree.mirror`
is. Everything reachable only through the proof term is renamed to
`_zk<16 hex>`, keyed by a salt.

The salt is 32 random bytes unless you pass `--salt`. Without it, recovering an
original name is a preimage search over SHA-256; with it, it is a lookup. Keep
it if you want to re-derive the mapping later, discard it if you do not.

`--include` moves the boundary: by default only the module you name counts as
"your development" and everything it imports is left alone and reached through
the artifact's import list, so a multi-module development needs
`--include M1,M2` for the other modules to be absorbed and obfuscated rather
than merely referenced.

`--hide-statement` obfuscates the statement's dependencies too. The verifier
then learns only that *some* theorem of *some* type checks — which is close to
vacuous on its own, and is meant to be combined with a commitment (below).

Honest limits on the hiding:

- The proof term's *shape* is fully visible. Its size, structure, and every
  external lemma it cites (`Nat.add_comm`, and so on) are in the file. Someone
  determined to understand your proof can.
- Names of imported constants are never touched — they have to resolve against
  the real environment.
- A sealed inductive keeps its `.rec`, `.leaf`, `.node` suffixes under the
  renamed prefix, because the kernel derives recursor names itself. The
  namespace *shape* leaks; the names do not.

## Sealing a whole repository

The headline operation, and the one-way one. It takes a Lean repository and
produces a standalone, obfuscated one; nothing in the output can reconstruct
the input, because the salt keying the name mangling is generated fresh and
discarded.

Run it under the *source* repository's `lake env`, so that repository's modules
are on the search path:

```console
$ cd my-conjectures
$ lake env /path/to/zklean . ../zk-conjectures
source      : .  (2 modules, package root /home/me/my-conjectures)
theorems    : 2 sealed
salt        : random, and discarded -- the mapping is not recoverable
merkle root : cc27c97a99aa9f36c9bae524722dba64766d8ae53648dde7bfa65e5436399145
output      : ../zk-conjectures
```

What the recipient gets, and what they can do with it:

```console
$ zklean check ../zk-conjectures/*.zkl.json
VALID    _zk8859ea58f678d97a.zkl.json
  statement   : Conjectures.AllReach 32 128
  declarations: 267 (standalone; all accepted by the kernel)
  axioms      : none
```

The claim is legible. The proof is 267 obfuscated declarations. The theorem's
own name, the module it lived in, and every lemma reached only through the
proof are gone. What survives is the statement's vocabulary — `AllReach`,
`step`, `reaches` — and it has to: an attestation to an unreadable claim
attests to nothing.

`test/fixtures/conjectures` is a working example of this shape — a conjecture
over a finite range, resolved by `decide`.

## Committing a whole development

`zklean commit` seals every theorem in a module and binds the results to one
Merkle root:

```console
$ zklean commit ZkLean.Demo
theorems    : 11
merkle root : 3f2b903f…
transcript  : zkl/transcript.json
```

You can then publish the root, disclose one artifact, and let anyone confirm it
is one of the things that root committed to — without showing them the rest.
`zklean/zklean.py` does that half in dependency-free Python, so a recipient with
no Lean toolchain can still check the commitment:

```console
$ python3 zklean/zklean.py verify zkl/transcript.json zkl/_zkb500….zkl.json
COMMITTED: zkl/_zkb500….zkl.json
  leaf   : thm:_zkb500dbb9abfb8676
  root   : 3f2b903f…
  note   : the Merkle commitment checks out. This does NOT check the
           proof itself -- run `zklean check …` for that.
```

Both implementations are pinned to the same test vectors, so they cannot drift.
A transcript commits to each artifact's **bytes**, so no verifier needs to
reproduce Lean's JSON serialiser to check one.

## Commands

```
zklean SRC DST                    seal a whole repository, one-way
zklean seal   MODULE [DECL ...]   seal declarations (default: every theorem in MODULE)
zklean check  ARTIFACT ...        re-check artifacts with the Lean kernel
zklean commit MODULE ...          seal everything and commit it to one Merkle root
zklean export ARTIFACT            re-emit for an independent checker

  -o, --out DIR            output directory (default: zkl)
      --salt S             fixed salt; reproducible, but invertible by anyone who
                           knows S. Default: fresh random salt, printed once.
      --hide-statement     obfuscate the target's statement as well as its proof
      --include M1,M2      also treat these modules as part of the sealed development
      --allow-axioms A,B   extra axioms `check` will tolerate
      --standalone         carry the whole closure; no Lean needed to check
      --format F           `ndjson` (nanoda_lib, lean4lean) or `legacy` (zkPi)
```

`check` exits 0 only if every artifact is `VALID`.

Sealing is deterministic given a salt: the same development and salt produce
byte-identical artifacts and the same root.

## Independent verification

An artifact sealed with `--standalone` carries its entire transitive closure,
down to `Nat` and `Eq`. It is checked against a *literally empty* environment
and needs no Lean installation, no `.olean` files, and no import path. For a
hand-written proof that is only a few dozen declarations:

| theorem | standalone closure |
| --- | --- |
| `0 + n = n` | 37 declarations |
| `sum_mirror` (inductive + recursion) | 59 declarations |
| `double_eq` (proved by `omega`) | 1381 declarations |

`zklean export` then re-emits a checked artifact in Lean's official
[NDJSON export format](https://github.com/leanprover/lean4export) (v3.1.0), so
an *independent* kernel can check it — no part of this repository is in that
trust path:

```console
$ zklean export zkl/_zk92f6….zkl.json -o out
$ nanoda_bin out/config.json
Checked 44 declarations with no typechecker errors
```

That is [`nanoda_lib`](https://github.com/ammkrn/nanoda_lib), a Lean 4 kernel
written in Rust. It accepts the sealed, obfuscated, standalone artifacts —
including a 1428-declaration `omega` proof pulling in nested inductives like
`Lean.Syntax` — and independently rejects the `sorry` fixture for depending on
`sorryAx`. Writing a *second* kernel here would have been a mistake: a kernel
that is only mostly right is an unsound verifier, which is worse than none.

## Prior art

**[zkPi](https://eprint.iacr.org/2024/267) (Laufer, Ozdemir & Boneh, Stanford,
ACM CCS 2024) already does step 3 below**, and does it properly: it is the first
zkSNARK for Lean proofs, built on CirC and Mirage over R1CS, with
implementations for both Lean 3 and Lean 4. Its statement is exactly the one
this roadmap targets — the prover holds a Lean proof of a public theorem `T`
and convinces a verifier without revealing the proof. Reported coverage for
Lean 4 is 43.4% of stdlib and 11.1% of mathlib, at up to 4.5 minutes per
theorem, with proofs short enough to "fit in Fermat's margin". Code:
[emlaufer/zkpi](https://github.com/emlaufer/zkpi).

`zklean export --format legacy` emits the line-based format zkPi reads, so
**you can bridge to it yourself** — install zkPi, point it at the file. We
neither bundle nor redistribute it, and take on none of its guarantees: whatever
zkPi concludes is between you and zkPi. That is deliberate. Emitting a file
format is not a derivative work, and this format is *Lean's* anyway — zkPi is a
consumer of it exactly as `nanoda_lib` is a consumer of the NDJSON one.

Tested, not assumed. Against zkPi built from `master`, on exports produced from
Lean v4.33.1 (zkPi pins v4.8.0-rc1, 25 versions earlier):

```console
$ zklean export art.zkl.json --format legacy -o out
$ zkpi out/_zk92f6….export list        # parses, lists the sealed theorem
$ zkpi out/_zk92f6….export count _zk92f6…
COUNT: 37
1614,1630,261,4052,5,136,8,5,4,1       # circuit sizes
```

**The version gap is not the binding constraint; zkPi's supported fragment is.**
It refuses recursion on inductive families with recursive parameters, and
`Nat.le` is one — so anything reaching for `≤` (`omega`, `decide` over a bounded
range, arithmetic `simp`) is outside what it can handle today, and fails with an
explicit panic rather than silently. Elementary equational proofs go through.
This is the same wall behind the paper's reported 43.4% / 11.1% coverage, and it
is worth knowing before planning around it: the finite-range combinatorial
statements that look most attractive for this use case are, today, mostly on the
wrong side of it.

What zkPi does **not** do, and what this repository is therefore about: it takes
an export you already have and proves a public statement. It does not obfuscate
a development, minimise a proof's closure, commit a repository to a Merkle root
for selective disclosure, audit axioms as a first-class verdict, or offer a
one-way repository-to-repository operation. Those are the parts built here.

Related but distinct:
[`is-my-lean-proof-vacuous`](https://github.com/LionSR/is-my-lean-proof-vacuous)
audits `#print axioms` to catch formalisations that compile but claim nothing —
the same insight as the audit here, aimed at fraud detection rather than
privacy, and with no cryptography.

## Roadmap to an actual zero-knowledge proof

The target statement is `∃ π. kernel(P, π) = accept`, with `P` public and `π`
private. Getting there needs three things. Two are done:

1. **A self-contained witness.** ✅ `--standalone` artifacts check against an
   empty environment. This is the hard prerequisite: a prover running inside a
   circuit or a zkVM receives a byte array and cannot open `.olean` files.
2. **An independent checker that consumes it.** ✅ `zklean export` speaks the
   standard export format, and `nanoda_lib` — plain Rust, no Lean — checks it.
3. **A proof of that checker's execution.** ❌ Not built here — and see
   [prior art](#prior-art), because zkPi has already done it. Either reuse zkPi
   (add a legacy-format emitter) or compile a checker to a zkVM guest, pass the
   witness as *private* input, and publish only the journal: the statement hash,
   the axiom list, and the accept bit.

Two cautions on the zkVM route. First, **a zkVM proof is succinct but not
automatically zero-knowledge** — in most zkVMs "zk" names succinctness, and
actual privacy requires an extra and expensive wrapping step. Getting that
wrong yields a proof that is short and leaks the witness anyway. Second, the
obstacle is cost, not architecture: a Lean kernel does unbounded definitional
equality search, so even the 44-declaration example above is millions of
cycles, and the 1428-declaration `omega` proof is likely out of reach without
shrinking the witness first.

Elementary, hand-written proofs — what most Erdős-style statements have — are
the tractable case, and are exactly where the closures measured above stay
small. That is also where `--standalone` minimisation earns its keep, since
circuit cost tracks witness size directly.

## Build

```console
lake build
./test/run.py
```

The suite cross-checks every export against an independent Lean kernel when one
is available. To enable that locally:

```console
git clone https://github.com/ammkrn/nanoda_lib && cd nanoda_lib && cargo build --release
ZKLEAN_NANODA=$PWD/target/release/nanoda_bin ./test/run.py
```

Without it those checks are skipped and say so; the rest of the suite is
unaffected.

The Lean-side vectors in `test/ZkLeanTests/Vectors.lean` run during `lake build`
via `#guard`, so a regression in SHA-256 or the Merkle construction breaks the
build rather than silently producing unverifiable artifacts.

**If the native build fails** with `clang: symbol lookup error: … undefined
symbol: … LLVM_22.1`, your distribution ships a `libLLVM.so` with the same
soname as the toolchain's. Point the loader at the toolchain's own copy:

```console
LD_LIBRARY_PATH="$(lake env printenv LEAN_SYSROOT)/lib" lake build
```

## Layout

```
ZkLean/Sha256.lean   SHA-256, self-contained, no Lean imports
ZkLean/Merkle.lean   domain-separated Merkle tree; wire-compatible with the Python verifier
ZkLean/Wire.lean     canonical JSON codec for Name / Level / Expr / ConstantInfo
ZkLean/Seal.lean     the obfuscating exporter
ZkLean/Check.lean    kernel replay and axiom audit
ZkLean/Export.lean   emitter for Lean's official NDJSON export format
ZkLean/Cli.lean      the command line
ZkLean/Demo.lean     a small development to seal, used by the tests
ZkLean/DemoAux.lean  a second module, so the tests can exercise --include
zklean/zklean.py     portable commitment verifier (Python 3.8+, stdlib only)
test/                adversarial fixtures, a dishonest prover, and the test suite
test/fixtures/       a separate Lean package, for testing whole-repository sealing
```
