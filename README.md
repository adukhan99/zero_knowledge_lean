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

**This is obfuscation with verifiability, not a zero-knowledge proof.** The
distinction matters, so it is worth being blunt about it.

The artifact *contains* the proof term — that is how the kernel can check it.
What sealing removes is everything around it: source text, comments,
docstrings, tactic scripts, file structure, every name your development
introduced, every binder name, every universe parameter name, and every
declaration the target does not depend on. What survives is a fully explicit
term that no human will read for pleasure, but that the kernel accepts or
rejects with no ambiguity.

A genuine zero-knowledge proof — one where the verifier learns *nothing* beyond
"a proof exists" — would require running Lean's type checker inside a
zk-SNARK/STARK circuit. That is a much larger and much riskier project, and
nothing here pretends to do it. What is offered instead is sound: the checking
is done by the actual Lean kernel, so a `VALID` verdict means what it says.

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
zklean seal   MODULE [DECL ...]   seal declarations (default: every theorem in MODULE)
zklean check  ARTIFACT ...        re-check artifacts with the Lean kernel
zklean commit MODULE ...          seal everything and commit it to one Merkle root

  -o, --out DIR            output directory (default: zkl)
      --salt S             fixed salt; reproducible, but invertible by anyone who
                           knows S. Default: fresh random salt, printed once.
      --hide-statement     obfuscate the target's statement as well as its proof
      --include M1,M2      also treat these modules as part of the sealed development
      --allow-axioms A,B   extra axioms `check` will tolerate
```

`check` exits 0 only if every artifact is `VALID`.

Sealing is deterministic given a salt: the same development and salt produce
byte-identical artifacts and the same root.

## Build

```console
lake build
./test/run.py
```

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
ZkLean/Cli.lean      the command line
ZkLean/Demo.lean     a small development to seal, used by the tests
ZkLean/DemoAux.lean  a second module, so the tests can exercise --include
zklean/zklean.py     portable commitment verifier (Python 3.8+, stdlib only)
test/                adversarial fixtures, a dishonest prover, and the test suite
```
