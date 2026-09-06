#!/usr/bin/env python3
"""End-to-end test suite for zklean.

Run from the repository root:

    ./test/run.py

Assumes `lake build` has already succeeded (the script will tell you if not).
The interesting half of this suite is the negative cases: a verifier that only
ever says VALID is worthless, so most of what follows constructs artifacts that
*must* be refused, and asserts that they are.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / ".lake" / "build" / "bin"
ZKLEAN = BIN / "zklean"
TAMPER = BIN / "zklean-tamper"
PYVERIFY = ROOT / "zklean" / "zklean.py"

# The toolchain's clang resolves libLLVM against the system copy on some
# distributions; pointing the loader at the toolchain's own lib fixes it.
TOOLCHAIN_LIB = Path(
    subprocess.run(["lake", "env", "printenv", "LEAN_SYSROOT"], cwd=ROOT,
                   capture_output=True, text=True).stdout.strip() or "/nonexistent") / "lib"

failures: list[str] = []
passes = 0


class Fatal(Exception):
    """A failure that makes every later assertion meaningless."""


def check(name: str, cond: bool, detail: str = "", fatal: bool = False) -> None:
    global passes
    if cond:
        passes += 1
        print(f"ok   {name}")
        return
    failures.append(name)
    print(f"FAIL {name}")
    if detail:
        for line in detail.strip().splitlines():
            print(f"       {line}")
    if fatal:
        raise Fatal(name)


def run(*args: str, expect: int | None = None) -> subprocess.CompletedProcess:
    env = dict(os.environ)
    if TOOLCHAIN_LIB.is_dir():
        env["LD_LIBRARY_PATH"] = f"{TOOLCHAIN_LIB}:{env.get('LD_LIBRARY_PATH', '')}"
    p = subprocess.run(["lake", "env", *args], cwd=ROOT, capture_output=True,
                       text=True, env=env)
    if expect is not None and p.returncode != expect:
        print(f"  (exit {p.returncode}, expected {expect})")
    return p


def verdicts(out: str) -> dict[str, str]:
    """Map artifact basename -> VALID / REJECTED / INVALID."""
    res = {}
    for line in out.splitlines():
        for word in ("VALID", "REJECTED", "INVALID"):
            if line.startswith(word):
                res[Path(line.split()[-1]).name] = word
                break
    return res


def main() -> int:
    if not ZKLEAN.exists() or not TAMPER.exists():
        print("build first:  lake build zklean zklean-tamper", file=sys.stderr)
        return 2

    tmp = Path(tempfile.mkdtemp(prefix="zklean-test-"))
    try:
        # ---------------------------------------------------------------
        # The portable verifier's own vectors, and its agreement with Lean.
        # ---------------------------------------------------------------
        p = subprocess.run([sys.executable, str(PYVERIFY), "selftest"],
                           capture_output=True, text=True)
        check("python merkle vectors", p.returncode == 0, p.stdout + p.stderr)

        # ---------------------------------------------------------------
        # Honest path: seal every theorem in the demo, commit, verify all.
        # ---------------------------------------------------------------
        out = tmp / "demo"
        p = run(str(ZKLEAN), "commit", "ZkLean.Demo", "--salt", "t", "-o", str(out),
                expect=0)
        check("commit succeeds", p.returncode == 0, p.stdout + p.stderr, fatal=True)

        transcript = out / "transcript.json"
        check("transcript written", transcript.exists(), fatal=True)
        t = json.loads(transcript.read_text())
        check("transcript format", t.get("format") == "zklean/v2", str(t.get("format")))
        check("transcript non-empty", t["leaf_count"] > 0)

        artifacts = sorted(q for q in out.glob("*.zkl.json"))
        check("one artifact per leaf", len(artifacts) == t["leaf_count"],
              f"{len(artifacts)} artifacts vs {t['leaf_count']} leaves")

        p = run(str(ZKLEAN), "check", *map(str, artifacts), expect=0)
        v = verdicts(p.stdout)
        check("every demo artifact is VALID",
              p.returncode == 0 and set(v.values()) == {"VALID"},
              p.stdout + p.stderr)

        # ---------------------------------------------------------------
        # Obfuscation actually happened.
        # ---------------------------------------------------------------
        names = [a.name for a in artifacts]
        check("target names are obfuscated",
              all(n.startswith("_zk") for n in names), ", ".join(names))
        body = (out / names[0]).read_text()
        check("no source text survives sealing",
              "theorem" not in body and "sorry" not in body and "--" not in body)

        # sum_mirror's statement stays readable while its proof does not.
        pp = run(str(ZKLEAN), "check", *map(str, artifacts)).stdout
        check("statements remain readable",
              "ZkLean.Demo.Tree.mirror" in pp and "ZkLean.Demo.Tree.sum" in pp,
              pp[:400])
        check("private helper names do not survive",
              "add_comm_nat" not in pp and "double_step" not in pp)

        # ---------------------------------------------------------------
        # The portable verifier agrees with the Lean one about commitments.
        # ---------------------------------------------------------------
        p = subprocess.run(
            [sys.executable, str(PYVERIFY), "verify", str(transcript), str(artifacts[0])],
            capture_output=True, text=True)
        check("python verifies a committed artifact", p.returncode == 0,
              p.stdout + p.stderr)

        # A byte-level edit must break the commitment.
        edited = tmp / "edited.zkl.json"
        edited.write_text(artifacts[0].read_text().replace('"sha256"', '"sha256 "'))
        p = subprocess.run(
            [sys.executable, str(PYVERIFY), "verify", str(transcript), str(edited)],
            capture_output=True, text=True)
        check("python rejects an edited artifact", p.returncode != 0,
              p.stdout + p.stderr)

        # A mismatched root must break the commitment.
        bad_t = tmp / "bad-transcript.json"
        t2 = json.loads(transcript.read_text())
        t2["root"] = "00" * 32
        bad_t.write_text(json.dumps(t2))
        p = subprocess.run(
            [sys.executable, str(PYVERIFY), "verify", str(bad_t), str(artifacts[0])],
            capture_output=True, text=True)
        check("python rejects a forged root", p.returncode != 0, p.stdout + p.stderr)

        # A declared root that does not match the declarations must be caught.
        forged = tmp / "forged-root.zkl.json"
        a0 = json.loads(artifacts[0].read_text())
        a0["root"] = "11" * 32
        forged.write_text(json.dumps(a0, indent=2) + "\n")
        p = run(str(ZKLEAN), "check", str(forged), expect=1)
        check("check rejects a forged artifact root",
              p.returncode == 1 and "commitment mismatch" in p.stdout,
              p.stdout + p.stderr)

        # ---------------------------------------------------------------
        # Unsound proofs: accepted by the kernel, refused by the audit.
        # ---------------------------------------------------------------
        adv = tmp / "adv"
        p = run(str(ZKLEAN), "seal", "ZkLeanTests.Adversarial", "--salt", "t",
                "-o", str(adv), expect=0)
        check("adversarial fixtures seal", p.returncode == 0, p.stdout + p.stderr)

        adv_files = sorted(adv.glob("*.zkl.json"))
        p = run(str(ZKLEAN), "check", *map(str, adv_files), expect=1)
        v = sorted(verdicts(p.stdout).values())
        check("axiom smuggling and sorry are REJECTED, honest proof is VALID",
              v == ["REJECTED", "REJECTED", "VALID"], p.stdout + p.stderr)
        check("check exits non-zero when anything is refused", p.returncode == 1)
        check("sorry is named as the reason", "depends on `sorry`" in p.stdout)

        # --allow-axioms is the documented escape hatch, and it works.
        sorry_file = [f for f in adv_files
                      if "sorryAx" in run(str(ZKLEAN), "check", str(f)).stdout]
        if sorry_file:
            p = run(str(ZKLEAN), "check", str(sorry_file[0]),
                    "--allow-axioms", "sorryAx", expect=0)
            check("--allow-axioms admits a named axiom",
                  p.returncode == 0 and "VALID" in p.stdout, p.stdout + p.stderr)
        else:
            check("--allow-axioms admits a named axiom", False, "no sorryAx artifact found")

        # ---------------------------------------------------------------
        # Tampering that recomputes the commitment correctly, so that only
        # the kernel can catch it.
        # ---------------------------------------------------------------
        honest = [f for f in adv_files
                  if verdicts(run(str(ZKLEAN), "check", str(f)).stdout).get(f.name) == "VALID"]
        check("found the honest adversarial fixture", len(honest) == 1)
        if honest:
            bad = tmp / "bad-proof.zkl.json"
            p = run(str(TAMPER), "replace-proof", str(honest[0]), str(bad), expect=0)
            check("tamper tool runs", p.returncode == 0, p.stdout + p.stderr)
            p = run(str(ZKLEAN), "check", str(bad), expect=1)
            check("kernel rejects a swapped proof term",
                  p.returncode == 1 and "type mismatch" in p.stdout,
                  p.stdout + p.stderr)

            donor = [f for f in adv_files if f != honest[0]][0]
            bad2 = tmp / "bad-statement.zkl.json"
            run(str(TAMPER), "swap-statement", str(honest[0]), str(donor), str(bad2))
            p = run(str(ZKLEAN), "check", str(bad2), expect=1)
            check("kernel rejects a swapped statement",
                  p.returncode == 1 and "INVALID" in p.stdout, p.stdout + p.stderr)

        # ---------------------------------------------------------------
        # Determinism, and the salt's effect.
        # ---------------------------------------------------------------
        d1, d2, d3 = tmp / "d1", tmp / "d2", tmp / "d3"
        run(str(ZKLEAN), "commit", "ZkLean.Demo", "--salt", "same", "-o", str(d1))
        run(str(ZKLEAN), "commit", "ZkLean.Demo", "--salt", "same", "-o", str(d2))
        run(str(ZKLEAN), "commit", "ZkLean.Demo", "--salt", "other", "-o", str(d3))
        r1 = json.loads((d1 / "transcript.json").read_text())["root"]
        r2 = json.loads((d2 / "transcript.json").read_text())["root"]
        r3 = json.loads((d3 / "transcript.json").read_text())["root"]
        check("same salt gives the same root", r1 == r2, f"{r1}\n{r2}")
        check("a different salt gives a different root", r1 != r3, f"{r1}\n{r3}")

        # ---------------------------------------------------------------
        # --include moves the boundary of "the sealed development".
        # ---------------------------------------------------------------
        TGT = "ZkLean.Demo.scale_one_eq"      # its proof reaches into ZkLean.DemoAux
        i0, i1 = tmp / "inc0", tmp / "inc1"
        run(str(ZKLEAN), "seal", "ZkLean.Demo", TGT, "--salt", "t", "-o", str(i0))
        run(str(ZKLEAN), "seal", "ZkLean.Demo", TGT, "--salt", "t",
            "--include", "ZkLean.DemoAux", "-o", str(i1))
        a0 = json.loads(next(i0.glob("*.zkl.json")).read_text())
        a1 = json.loads(next(i1.glob("*.zkl.json")).read_text())
        imports0 = [".".join(i) for i in a0["imports"]]
        imports1 = [".".join(i) for i in a1["imports"]]
        check("without --include, the other module is an import",
              "ZkLean.DemoAux" in imports0, str(imports0))
        check("with --include, the other module is absorbed",
              "ZkLean.DemoAux" not in imports1, str(imports1))
        check("absorbing a module adds its declarations to the artifact",
              len(a1["constants"]) > len(a0["constants"]),
              f"{len(a0['constants'])} -> {len(a1['constants'])}")
        p = run(str(ZKLEAN), "check", *[str(f) for f in (*i0.glob("*.json"), *i1.glob("*.json"))],
                expect=0)
        check("both sides of the boundary verify",
              p.returncode == 0 and set(verdicts(p.stdout).values()) == {"VALID"},
              p.stdout + p.stderr)

        # An absorbed module's names are still public when the *statement*
        # mentions them; --hide-statement is what removes them.
        i2 = tmp / "inc2"
        run(str(ZKLEAN), "seal", "ZkLean.Demo", TGT, "--salt", "t",
            "--include", "ZkLean.DemoAux", "--hide-statement", "-o", str(i2))
        f2 = next(i2.glob("*.zkl.json"))
        check("--hide-statement removes an absorbed module's names",
              "DemoAux" not in f2.read_text())
        p = run(str(ZKLEAN), "check", str(f2), expect=0)
        check("fully hidden cross-module artifact still verifies",
              p.returncode == 0 and "VALID" in p.stdout, p.stdout + p.stderr)

        # ---------------------------------------------------------------
        # --hide-statement really does hide the statement.
        # ---------------------------------------------------------------
        hidden = tmp / "hidden"
        run(str(ZKLEAN), "seal", "ZkLean.Demo", "ZkLean.Demo.sum_mirror",
            "--salt", "t", "--hide-statement", "-o", str(hidden))
        hf = list(hidden.glob("*.zkl.json"))
        check("hidden-statement artifact written", len(hf) == 1)
        if hf:
            p = run(str(ZKLEAN), "check", str(hf[0]), expect=0)
            check("hidden-statement artifact still verifies",
                  p.returncode == 0 and "VALID" in p.stdout, p.stdout + p.stderr)
            check("hidden-statement artifact leaks no names",
                  "Tree" not in hf[0].read_text(), hf[0].read_text()[:300])

    except Fatal as e:
        print(f"\naborted: {e} failed, so the remaining checks were skipped")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print()
    print(f"{passes} passed, {len(failures)} failed")
    for f in failures:
        print(f"  failed: {f}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
