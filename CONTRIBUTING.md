# Contributing to zklean

Thanks for looking. This file is the practical companion to the
[README](README.md): the README says what the tool does, this says how it is
put together, what the non-negotiables are, and where help would actually move
things.

## Read this part first

**zklean is a verification tool, and the worst possible bug is a false
`VALID`.** Everything below follows from that.

A tool that wrongly rejects a good proof is annoying. A tool that wrongly
accepts a bad one is worse than not existing, because someone will rely on it.
If you are weighing a change that makes `check` more permissive against one
that makes it stricter, take the stricter one and open an issue about the
false negative.

**We do not own the cryptography.** The zkSNARK over Lean proofs is
[zkPi](https://eprint.iacr.org/2024/267) (Laufer, Ozdemir & Boneh, CCS 2024),
and we will not be reimplementing it. Patches that add a hand-rolled proof
system will be declined, however good — an under-tested SNARK is an unsound
verifier. What we own is the layer around it: closure minimisation,
obfuscation, commitment, the axiom audit, and the export formats independent
checkers read. See [Prior art](README.md#prior-art) for the boundary.

## Setting up

```console
git clone https://github.com/adukhan99/zero_knowledge_lean && cd zero_knowledge_lean
lake build zklean zklean-tamper ZkLeanTests
./test/run.py
```

The `#guard` vectors in `test/ZkLeanTests/Vectors.lean` run *during* `lake
build`, so a regression in SHA-256 or the Merkle construction breaks the build
rather than quietly producing unverifiable artifacts.

**If the native build fails** with `clang: symbol lookup error: … undefined
symbol: … LLVM_22.1`, your distribution ships a `libLLVM.so` with the same
soname as the Lean toolchain's, and the loader is picking the wrong one:

```console
LD_LIBRARY_PATH="$(lake env printenv LEAN_SYSROOT)/lib" lake build
```

### The external checkers

The interesting half of the test suite is cross-implementation. Without these,
the export tests only confirm we agree with ourselves.

**`nanoda_lib`** — a Lean 4 kernel in Rust. Reads our NDJSON output.

```console
git clone https://github.com/ammkrn/nanoda_lib && cd nanoda_lib && cargo build --release
export ZKLEAN_NANODA=$PWD/target/release/nanoda_bin
```

**zkPi** — the zkSNARK. Reads our legacy output. Harder to build, and two
things will bite you:

```console
git clone --recurse-submodules https://github.com/emlaufer/zkpi && cd zkpi
rustup toolchain install nightly-2023-12-03 --profile minimal
CFLAGS=-std=gnu17 cargo +nightly-2023-12-03 build --release
export ZKLEAN_ZKPI=$PWD/target/release/zkpi
```

It pins a 2023 nightly, and its GMP dependency will not configure under GCC 14+
without `CFLAGS=-std=gnu17` — C23 changed `void g(){}` from "unspecified
parameters" to "none", which breaks a GMP configure probe. CI deliberately does
not build zkPi for this reason; the legacy tests validate structurally without
it and say so when it is absent.

With both set, `./test/run.py` runs 83 checks. With neither it runs 67 and
prints which it skipped — so the cross-implementation half is exactly those 16.

## How it fits together

Layered, and acyclic. `Sha256` stands alone; `Merkle` and `Wire` each build on
it; `Seal` combines those two, and `Check` → `Export` → `Cli` is then a
straight chain. Reading in table order works.

| module | lines | what it owns |
| --- | --- | --- |
| `Sha256.lean` | 118 | SHA-256. No `Lean` import at all, so the commitment layer is auditable on its own. |
| `Merkle.lean` | 92 | Domain-separated Merkle tree. Byte-compatible with `zklean/zklean.py`. |
| `Wire.lean` | 262 | Canonical JSON codec for `Name` / `Level` / `Expr` / `ConstantInfo`. The security boundary for decoding. |
| `Seal.lean` | 261 | The obfuscating exporter: closure, rename map, scrubbing. |
| `Check.lean` | 173 | Kernel replay and axiom audit. |
| `Export.lean` | 482 | Emitters for both interchange formats. |
| `Cli.lean` | 461 | Commands, option parsing, repository sealing. |

`zklean/zklean.py` is a separate, deliberately dependency-free Python verifier
for the *commitment* only. It does not check proofs and must never pretend to.

Other checkers read these formats — `lean4lean` reads the NDJSON one — but
`nanoda_lib` and zkPi are the two this repository actually tests against, and
only tested claims go in the docs.

### The pipeline

```
Lean repo ──seal──▶ artifact ──check──▶ verdict
                       │
                       └──export──▶ NDJSON  ──▶ nanoda_lib   (tested here)
                                    legacy   ──▶ zkPi ──▶ zkSNARK   (tested here)
```

## Non-negotiables

Four rules, each of which exists because breaking it produced a real bug here.

**1. Never believe a field in an artifact — recompute it.** The Merkle root and
the statement digest are *not* evidence: anyone editing the declarations can
recompute both, which is exactly what `Artifact.reseal` does for the test
suite. Only the kernel replay and the axiom audit carry weight. If you add a
field, either the verifier derives it independently or it is documentation and
labelled as such. This is why `declared_axioms` was removed from the format.

**2. The kernel is the authority; our code is plumbing.** `check` hands
declarations to `Lean.Environment.replay` at trust level 0. Do not add a
fast path that skips it, and do not add a check that *substitutes* for it.

**3. Every rejection path needs a test that proves it still bites.** A
validator that accepts everything passes every positive test. `test/run.py`
therefore includes negative controls — a dangling index, a tampered proof term,
a smuggled axiom, a `sorry`. If you add a validator, add its negative control
in the same commit.

**4. Numbers in the docs are measured, not estimated.** Every figure in the
README was produced by running the tool. If you change something that moves a
number, re-measure it. Two of them (`nanoda_lib`'s declaration counts, zkPi's
circuit sizes) come from other people's tools and cannot be guessed at.

## Where help would actually move things

Roughly ordered by value, with honest difficulty.

**zkPi's supported fragment — hard, upstream, highest value.** zkPi refuses
recursion on inductive families with recursive parameters, and `Nat.le` is one.
That takes out `omega`, arithmetic `simp`, and `decide` over a bounded range —
so bounded quantification, which is the natural shape of finite combinatorial
claims. It is the wall behind the paper's 43.4% / 11.1% coverage, and lifting
it is worth more than anything on this list. That work belongs in zkPi, not
here; we can help by supplying minimal failing exports.

**An NDJSON front end for zkPi — medium, upstream.** zkPi reads the legacy
format at Lean `v4.8.0-rc1`. The format has since moved to NDJSON v3.1.0.
Teaching zkPi the newer format would remove a whole class of drift. We already
emit both, so the exports to test against exist.

**Closure minimisation — medium, here.** Circuit cost tracks witness size
directly, so shrinking the closure directly widens what is affordable. An
`omega` proof carries 1356 declarations against 22–48 for an elementary one.
Some of that is irreducible; some is almost certainly not.

**Hiding the leaf position — medium, here, well-specified.** A plain Merkle
path reveals *which* leaf you opened. For "prove this theorem is in the
committed repository without saying which one", that leaks. Wants a hiding
set-membership scheme rather than a bare path.

**Mutual inductive blocks in the legacy emitter — small, here.** The reference
exporter emits one `#IND` per type and we match that, but no test covers a
genuinely mutual block. Add a fixture, confirm it round-trips, or find out it
doesn't.

**More fixtures — small, valuable, good first contribution.** The worked
example is deliberately thin. Real theorems from real developments, screened
against both checkers, would tell us far more about coverage than we currently
know. See `test/fixtures/conjectures/README.md`.

## Gotchas we already paid for

Lean-4-internals knowledge that cost real debugging time. Worth reading before
you start.

- **`Environment.find?` cannot see what `replay` added.** It consults the
  imported constant map and async branches only. Using it for the axiom audit
  makes the audit *vacuously pass* — a silently unsound verifier. Always go
  through `findConst?`.
- **Recursor names are kernel-derived, and not always `T.rec`.** A mutual or
  nested inductive block yields `T.rec_1`, `T.rec_2`, … Constructing the names
  by hand is wrong, and wrong only for nested inductives — which `omega` drags
  in via `Lean.Syntax`, so your small tests will not catch it. Read them from
  the environment (`recursorsByFamily`).
- **`isReservedName` does not cover lemmas derived from an inductive type.** It
  answers `false` for `Tree.leaf.injEq` and friends, and every generated lemma
  carries a source position, so declaration ranges do not separate them either.
  Hence the component-matching heuristic in `isGeneratedName`.
- **Some names are privileged by the kernel.** `Nat` backs literal arithmetic,
  so renaming it breaks `Expr.lit`. Standalone sealing therefore never renames
  imported names; the three standard axioms must also stay recognisable to the
  audit.
- **`seal` is a reserved keyword in Lean 4.** So is `unseal`. Hence `sealDecl`.
- **Structure instances are column-sensitive.** A continuation line indented
  less than the opening `{` silently ends the instance. Bind fields to `let`s
  first, or keep it on one line.
- **`←` inside a structure instance field needs parentheses.** `value := ← e`
  does not parse; `value := (← e)` does.
- **zkPi writes `COUNT:` to stderr, not stdout.** A test grepping stdout will
  report a working pipeline as broken.
- **Byte fidelity matters in the legacy format.** The reference exporter leaves
  a trailing space where a level-parameter list is empty. We reproduce that
  deliberately rather than assume a consumer's parser is tolerant.

## Conventions

**Tests.** `test/run.py` is the suite; add to it. A check gets a sentence-long
name that reads as a claim (`"kernel rejects a swapped proof term"`), so a
failure line says what broke without opening the file. Prefer asserting on
names over counts — count assertions break every time a fixture grows.

**Comments** explain *why*, especially where the code looks odd. Most of the
odd-looking code here is odd because of something in the Gotchas list; say
which.

**Commits.** Plain prose describing what changed and why, wrapped at ~76
columns. Mention what you measured. If you found a bug while doing something
else, say so — the discovery path is often the most useful part.

**Scope.** Small, reviewable commits over large ones. If a change touches both
the sealing and checking sides, say in the message why it has to.

## Reporting a soundness bug

If you find a way to make `check` say `VALID` for something that should not be:
that is the most important bug class in the project. Open an issue with the
artifact and the command, or if you would rather not post it publicly, say so
in the issue and we will sort out a private channel. Please do not sit on it.
