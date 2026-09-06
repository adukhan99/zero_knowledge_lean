/-
Pure, kernel-reducible SHA-256 over bytes (FIPS 180-4).

Self-contained: no `Lean` imports, so the commitment layer can be audited
independently of the metaprogramming layer.
-/

namespace ZkLean

abbrev Word := UInt32

/-- Right-rotate a 32-bit word by `n` bits (`0 < n < 32`). -/
def ror (n : Nat) (x : Word) : Word :=
  (x >>> n.toUInt32) ||| (x <<< (32 - n).toUInt32)

def Ch (x y z : Word) : Word := (x &&& y) ^^^ ((~~~x) &&& z)
def Maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bigSigma0 (x : Word) : Word := (ror 2 x) ^^^ (ror 13 x) ^^^ (ror 22 x)
def bigSigma1 (x : Word) : Word := (ror 6 x) ^^^ (ror 11 x) ^^^ (ror 25 x)
def smallSigma0 (x : Word) : Word := (ror 7 x) ^^^ (ror 18 x) ^^^ (x >>> (3 : UInt32))
def smallSigma1 (x : Word) : Word := (ror 17 x) ^^^ (ror 19 x) ^^^ (x >>> (10 : UInt32))

/-- Round constants: fractional parts of the cube roots of the first 64 primes. -/
def K : Array Word := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Initial state: fractional parts of the square roots of the first 8 primes. -/
def H0 : Array Word :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Big-endian encode a `UInt64` as 8 bytes. -/
private def be64 (n : UInt64) : ByteArray :=
  (List.range 8).foldl (fun acc i => acc.push ((n >>> ((7 - i) * 8).toUInt64).toUInt8))
    ByteArray.empty

/-- FIPS 180-4 §5.1.1 padding to a multiple of 64 bytes. -/
def pad (msg : ByteArray) : ByteArray :=
  let l := msg.size
  let total := ((l + 9 + 63) / 64) * 64
  let zeros := total - (l + 9)
  let body := (List.range zeros).foldl (fun acc _ => acc.push 0) (msg.push 0x80)
  body ++ be64 (l * 8).toUInt64

/-- Read 4 big-endian bytes at `off`. -/
def bytesToWord (b : ByteArray) (off : Nat) : Word :=
  (b[off]!.toUInt32 <<< (24 : UInt32)) ||| (b[off + 1]!.toUInt32 <<< (16 : UInt32))
    ||| (b[off + 2]!.toUInt32 <<< (8 : UInt32)) ||| b[off + 3]!.toUInt32

/-- Extend the first 16 message words into the full 64-word schedule. -/
def schedule (w0 : Array Word) : Array Word :=
  (List.range 48).foldl (fun w i =>
      let j := i + 16
      w.push (smallSigma1 w[j - 2]! + w[j - 7]! + smallSigma0 w[j - 15]! + w[j - 16]!))
    w0

/-- Compress one 64-byte block into the running state. -/
def compress (state : Array Word) (block : ByteArray) : Array Word :=
  let w := schedule ((List.range 16).foldl (fun acc i => acc.push (bytesToWord block (i * 4))) #[])
  let v := (List.range 64).foldl (fun st i =>
      let a := st[0]!; let b := st[1]!; let c := st[2]!; let d := st[3]!
      let e := st[4]!; let f := st[5]!; let g := st[6]!; let h := st[7]!
      let t1 := h + bigSigma1 e + Ch e f g + K[i]! + w[i]!
      let t2 := bigSigma0 a + Maj a b c
      #[t1 + t2, a, b, c, d + t1, e, f, g])
    state
  (List.range 8).foldl (fun acc i => acc.push (v[i]! + state[i]!)) #[]

/-- SHA-256 of a byte array. -/
def sha256 (msg : ByteArray) : ByteArray :=
  let padded := pad msg
  let final := (List.range (padded.size / 64)).foldl
    (fun st i => compress st (padded.extract (i * 64) (i * 64 + 64))) H0
  final.foldl (fun acc word =>
      (List.range 4).foldl (fun a bi => a.push ((word >>> ((3 - bi) * 8).toUInt32).toUInt8)) acc)
    ByteArray.empty

/-- SHA-256 of a string's UTF-8 encoding. -/
def sha256s (s : String) : ByteArray := sha256 s.toUTF8

private def hexDigits : Array Char :=
  #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']

/-- Lowercase hex encoding. -/
def toHex (b : ByteArray) : String :=
  b.foldl (fun out byte =>
      out.push hexDigits[byte.toNat / 16]! |>.push hexDigits[byte.toNat % 16]!)
    ""

private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode lowercase-or-uppercase hex; `none` on any invalid input. -/
def ofHex? (s : String) : Option ByteArray :=
  let cs := s.toList
  if cs.length % 2 != 0 then none
  else
    let rec go (acc : ByteArray) : List Char → Option ByteArray
      | [] => some acc
      | hi :: lo :: rest => do
          let h ← hexVal? hi
          let l ← hexVal? lo
          go (acc.push (h * 16 + l).toUInt8) rest
      | _ => none
    go ByteArray.empty cs

end ZkLean
