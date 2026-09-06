/-
Test vectors for the commitment layer, evaluated at elaboration time.

`#guard` runs these through the Lean interpreter while the module is compiled,
so `lake build` fails if any of them regresses. The Merkle values are shared
with `zklean/zklean.py selftest`, which pins the two implementations to each
other -- a divergence would silently make artifacts unverifiable by whichever
side is wrong.
-/
import ZkLean.Merkle

namespace ZkLeanTests
open ZkLean

/-! ## SHA-256 (FIPS 180-4 / NIST) -/

#guard toHex (sha256s "") ==
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard toHex (sha256s "abc") ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
-- 56 bytes: exercises the two-block padding boundary.
#guard toHex (sha256s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard toHex (sha256s (String.ofList (List.replicate 1000 'a'))) ==
  "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
#guard toHex (sha256s "The quick brown fox jumps over the lazy dog") ==
  "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592"

/-! ## Hex round-tripping -/

#guard ofHex? (toHex (sha256s "x")) == some (sha256s "x")
#guard ofHex? "zz" == none
#guard ofHex? "abc" == none   -- odd length
#guard ofHex? "" == some ByteArray.empty

/-! ## Merkle, cross-checked against `zklean.py selftest` -/

#guard toHex emptyHash ==
  "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d"
#guard toHex (rootOf (levels #[])) == toHex emptyHash
#guard toHex (commit #[("a", "one"), ("b", "two"), ("c", "three")]).1 ==
  "65f64b6bdbed35080bb08f9a367fb30d7a9272c26e929ec1a2351e7fb11b2e40"
-- A single leaf is its own root: no padding, no nodes.
#guard toHex (commit #[("a", "one")]).1 == toHex (leafHash "one")
-- Leaves are committed in id order, so input order must not matter.
#guard (commit #[("b", "two"), ("a", "one")]).1 == (commit #[("a", "one"), ("b", "two")]).1

#guard nextPow2 0 == 1
#guard nextPow2 1 == 1
#guard nextPow2 5 == 8
#guard nextPow2 8 == 8

/-- Every leaf's audit path must fold back to the root. -/
private def pathsAgree (entries : Array (String × String)) : Bool :=
  let (root, sorted, proofs) := commit entries
  (List.range sorted.size).all fun i =>
    verifyProof root (leafHash sorted[i]!.2) proofs[i]!

#guard pathsAgree #[("a", "one")]
#guard pathsAgree #[("a", "one"), ("b", "two"), ("c", "three")]
#guard pathsAgree #[("a", "1"), ("b", "2"), ("c", "3"), ("d", "4"), ("e", "5")]

-- A path must not fold back to the root for content it does not commit to.
#guard
  let (root, sorted, proofs) := commit #[("a", "one"), ("b", "two"), ("c", "three")]
  !verifyProof root (leafHash "forged") proofs[0]! && sorted.size == 3

end ZkLeanTests
