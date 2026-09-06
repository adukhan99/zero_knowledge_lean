# zklean.py — portable commitment verifier

The dependency-free half of zklean: Python 3.8+, standard library only, no Lean
toolchain required.

It answers one question: **is this artifact the one that root committed to?**

    python3 zklean/zklean.py root     TRANSCRIPT            print the Merkle root
    python3 zklean/zklean.py list     TRANSCRIPT            list committed leaves
    python3 zklean/zklean.py verify   TRANSCRIPT ARTIFACT   check the commitment
    python3 zklean/zklean.py selftest                       run shared test vectors

It deliberately does **not** check proofs. Deciding whether a sealed artifact is
a valid Lean proof needs the Lean kernel, and this file does not reimplement it
— use `zklean check ARTIFACT` for that. The division of labour is the point: a
recipient with no Lean install can still confirm the commitment, and a recipient
with Lean can additionally confirm the proof.

The Merkle construction is identical to `ZkLean/Merkle.lean`:

    leaf(content)     = SHA256(0x00 || utf8(content))
    node(left, right) = SHA256(0x01 || left || right)
    empty pad         = SHA256(0x00)

Leaves are sorted by id and padded to a power of two with the empty pad. A
transcript commits to each artifact's **file bytes**, so verifying one never
requires reproducing Lean's JSON serialiser.

`selftest` shares its vectors with `test/ZkLeanTests/Vectors.lean`, so the two
implementations are pinned to each other and cannot drift apart unnoticed.

See the [top-level README](../README.md) for the full picture.
