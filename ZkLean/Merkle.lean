/-
Domain-separated binary Merkle tree over sorted leaves.

Wire-compatible with the portable Python verifier in `zklean/zklean.py`:

    leaf(content)     = SHA256(0x00 ‖ utf8(content))
    node(left, right) = SHA256(0x01 ‖ left ‖ right)
    empty pad         = SHA256(0x00)

Leaves are sorted by id and padded with the empty pad to a power of two.
-/
import ZkLean.Sha256

namespace ZkLean

/-- `SHA256(0x00 ‖ utf8 content)`: the commitment to one leaf's content. -/
def leafHash (content : String) : ByteArray :=
  sha256 ((ByteArray.empty.push 0x00) ++ content.toUTF8)

/-- `SHA256(0x01 ‖ left ‖ right)`: an internal node. -/
def nodeHash (left right : ByteArray) : ByteArray :=
  sha256 (((ByteArray.empty.push 0x01) ++ left) ++ right)

/-- `SHA256(0x00)`: the padding leaf, and the root of an empty tree. -/
def emptyHash : ByteArray := sha256 (ByteArray.empty.push 0x00)

/-- Smallest power of two `≥ n` (and `≥ 1`). -/
def nextPow2 (n : Nat) : Nat :=
  let rec go (m fuel : Nat) : Nat :=
    match fuel with
    | 0 => m
    | fuel + 1 => if n ≤ m then m else go (m * 2) fuel
  go 1 n

/-- Combine adjacent pairs of a row. Assumes `row.size` is even. -/
private def pairUp (row : Array ByteArray) : Array ByteArray :=
  (List.range (row.size / 2)).foldl (fun acc i => acc.push (nodeHash row[2 * i]! row[2 * i + 1]!)) #[]

private def levelsGo (row : Array ByteArray) (acc : Array (Array ByteArray)) :
    Nat → Array (Array ByteArray)
  | 0 => acc
  | fuel + 1 =>
    if row.size ≤ 1 then acc
    else let next := pairUp row; levelsGo next (acc.push next) fuel

/-- All tree levels bottom-up: `levels[0]` is the padded leaf row, the last is
the singleton root row. `#[]` only when there are no leaves. -/
def levels (leafHashes : Array ByteArray) : Array (Array ByteArray) :=
  if leafHashes.isEmpty then #[]
  else
    let size := nextPow2 leafHashes.size
    let bottom := leafHashes ++ Array.replicate (size - leafHashes.size) emptyHash
    levelsGo bottom #[bottom] size

/-- The Merkle root. An empty tree commits to `emptyHash`. -/
def rootOf (ls : Array (Array ByteArray)) : ByteArray :=
  match ls.back? with
  | some row => row[0]!
  | none => emptyHash

/-- One step of an audit path. `left` is true when the *sibling* is the left child. -/
structure Step where
  sibling : ByteArray
  left    : Bool
  deriving Inhabited

/-- Audit path for leaf `idx`, bottom-up. -/
def proofOf (ls : Array (Array ByteArray)) (idx : Nat) : Array Step :=
  (List.range (ls.size - 1)).foldl
    (fun (acc, pos) d =>
      let row := ls[d]!
      let step := if pos % 2 == 0 then ⟨row[pos + 1]!, false⟩ else ⟨row[pos - 1]!, true⟩
      (acc.push step, pos / 2))
    ((#[] : Array Step), idx) |>.1

/-- Fold an audit path from a leaf hash up to a candidate root. -/
def applyProof (leaf : ByteArray) (path : Array Step) : ByteArray :=
  path.foldl (fun h s => if s.left then nodeHash s.sibling h else nodeHash h s.sibling) leaf

/-- Check that `leaf` is committed by `root` via `path`. -/
def verifyProof (root leaf : ByteArray) (path : Array Step) : Bool :=
  toHex (applyProof leaf path) == toHex root

/-- Commit a list of `(id, content)` leaves: sorts by id, returns the root, the
sorted ids, and each leaf's audit path. -/
def commit (entries : Array (String × String)) :
    ByteArray × Array (String × String) × Array (Array Step) :=
  let sorted := entries.qsort (fun a b => a.1 < b.1)
  let ls := levels (sorted.map (fun e => leafHash e.2))
  (rootOf ls, sorted, (Array.range sorted.size).map (proofOf ls))

end ZkLean
