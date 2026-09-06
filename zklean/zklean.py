#!/usr/bin/env python3
"""zklean -- portable verifier for zklean commitments.

This is the *commitment* half of zklean, in dependency-free Python. It checks
that a sealed artifact is the one a transcript's Merkle root commits to, on any
machine with Python 3.8+ and no Lean toolchain.

It deliberately does NOT check proofs. Deciding whether a sealed artifact is a
valid Lean proof requires the Lean kernel, and this file does not pretend to
reimplement it -- run `zklean check ARTIFACT` for that. What you get here is:

    root       print a transcript's Merkle root
    list       list the committed leaves
    verify     check one artifact against a transcript (or a standalone
               disclosure) -- recomputes the leaf hash and folds the audit path
    selftest   run the built-in test vectors

So a recipient with no Lean install can still confirm "this artifact is exactly
the one that root commits to"; a recipient with Lean can additionally confirm
"and the kernel accepts it".

Merkle construction (identical to ZkLean/Merkle.lean, cross-checked in tests):

    leaf(content)     = SHA256(0x00 || utf8(content))
    node(left, right) = SHA256(0x01 || left || right)
    empty pad         = SHA256(0x00)

Leaves are sorted by id and padded to a power of two with the empty pad.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

FORMAT = "zklean/v2"
ARTIFACT_FORMAT = "zklean-seal/v1"
VERSION = "2.0.0"

EMPTY_PAD = hashlib.sha256(b"\x00").digest()


def leaf_hash(content: str) -> bytes:
    return hashlib.sha256(b"\x00" + content.encode("utf-8")).digest()


def node_hash(left: bytes, right: bytes) -> bytes:
    return hashlib.sha256(b"\x01" + left + right).digest()


def merkle_root(entries: List[Tuple[str, str]]) -> bytes:
    """Root over (id, content) pairs, sorted by id and padded to a power of two."""
    if not entries:
        return EMPTY_PAD
    hashes = [leaf_hash(c) for _, c in sorted(entries, key=lambda e: e[0])]
    size = 1
    while size < len(hashes):
        size *= 2
    row = hashes + [EMPTY_PAD] * (size - len(hashes))
    while len(row) > 1:
        row = [node_hash(row[i], row[i + 1]) for i in range(0, len(row), 2)]
    return row[0]


def apply_path(leaf: bytes, path: List[Dict[str, Any]]) -> bytes:
    """Fold an audit path from a leaf hash up to a candidate root."""
    h = leaf
    for step in path:
        sib = bytes.fromhex(step["sibling"])
        h = node_hash(sib, h) if step["left"] else node_hash(h, sib)
    return h


def load(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def cmd_root(args: argparse.Namespace) -> int:
    print(load(Path(args.transcript))["root"])
    return 0


def cmd_list(args: argparse.Namespace) -> int:
    t = load(Path(args.transcript))
    for leaf in t["leaves"]:
        print(f"{leaf['id']}\t{leaf.get('artifact', '')}")
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    t = load(Path(args.transcript))
    if t.get("format") != FORMAT:
        print(f"INVALID: unsupported transcript format {t.get('format')!r}", file=sys.stderr)
        return 1
    root = t["root"]

    artifact_text = Path(args.artifact).read_text(encoding="utf-8")
    artifact = json.loads(artifact_text)
    if artifact.get("format") != ARTIFACT_FORMAT:
        print(f"INVALID: unsupported artifact format {artifact.get('format')!r}", file=sys.stderr)
        return 1

    # A transcript commits to the artifact file's bytes verbatim, so there is
    # no canonicalisation step to get wrong or to disagree with Lean about.
    h = leaf_hash(artifact_text)

    leaf_id = args.id
    if leaf_id is None:
        matches = [l for l in t["leaves"] if l["content_hash"] == h.hex()]
        if not matches:
            print(f"INVALID: no leaf of {args.transcript} commits to {args.artifact}")
            print(f"  artifact hashes to {h.hex()}")
            return 1
        leaf = matches[0]
    else:
        found = [l for l in t["leaves"] if l["id"] == leaf_id]
        if not found:
            print(f"INVALID: no leaf with id {leaf_id}", file=sys.stderr)
            return 1
        leaf = found[0]
        if leaf["content_hash"] != h.hex():
            print(f"INVALID: {leaf_id} commits to {leaf['content_hash']}, "
                  f"but {args.artifact} hashes to {h.hex()}")
            return 1

    computed = apply_path(h, leaf["proof"]).hex()
    if computed != root:
        print(f"INVALID: audit path for {leaf['id']} leads to {computed}, not {root}")
        return 1

    print(f"COMMITTED: {args.artifact}")
    print(f"  leaf   : {leaf['id']}")
    print(f"  root   : {root}")
    print(f"  note   : the Merkle commitment checks out. This does NOT check the")
    print(f"           proof itself -- run `zklean check {args.artifact}` for that.")
    return 0


def cmd_selftest(_args: argparse.Namespace) -> int:
    """Test vectors shared with ZkLean/Merkle.lean, so the two implementations
    are pinned to each other."""
    checks = [
        ("empty pad", EMPTY_PAD.hex(),
         "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d"),
        ("empty tree", merkle_root([]).hex(),
         "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d"),
        ("three leaves",
         merkle_root([("a", "one"), ("b", "two"), ("c", "three")]).hex(),
         "65f64b6bdbed35080bb08f9a367fb30d7a9272c26e929ec1a2351e7fb11b2e40"),
        ("single leaf", merkle_root([("a", "one")]).hex(), leaf_hash("one").hex()),
    ]
    ok = True
    for name, got, want in checks:
        status = "ok  " if got == want else "FAIL"
        if got != want:
            ok = False
        print(f"{status} {name}: {got}")
        if got != want:
            print(f"     expected: {want}")
    return 0 if ok else 1


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        prog="zklean.py",
        description="Portable verifier for zklean Merkle commitments "
                    "(does not check proofs; use `zklean check` for that).")
    sub = p.add_subparsers(dest="command", required=True)

    p_root = sub.add_parser("root", help="print a transcript's Merkle root")
    p_root.add_argument("transcript")
    p_root.set_defaults(func=cmd_root)

    p_list = sub.add_parser("list", help="list committed leaves")
    p_list.add_argument("transcript")
    p_list.set_defaults(func=cmd_list)

    p_ver = sub.add_parser("verify", help="check an artifact against a transcript")
    p_ver.add_argument("transcript")
    p_ver.add_argument("artifact")
    p_ver.add_argument("--id", default=None,
                       help="require this leaf id (default: locate by content hash)")
    p_ver.set_defaults(func=cmd_verify)

    p_self = sub.add_parser("selftest", help="run shared test vectors")
    p_self.set_defaults(func=cmd_selftest)

    args = p.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
