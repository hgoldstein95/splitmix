import SplitMix
import Tests.Eval

open SplitMix

/-! `lake test`: agreement between the C code and the Lean spec, edge cases,
and a uniformity check. -/

def check (failures : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    IO.eprintln s!"FAIL: {name}"
    failures.modify (· + 1)

/-- Random bounds of every magnitude from 0 to 2^80, compared against the spec. -/
def agreement (check : String → Bool → IO Unit) : IO Unit := do
  let mut g := ofSeed 12345
  for i in [0:20000] do
    let bits := i % 81
    let (lo, g') := randNatRef g 0 (2 ^ bits); g := g'
    let (hi, g') := randNatRef g 0 (2 ^ bits); g := g'
    let (h, g') := split g; g := g'
    check s!"randNat agrees on {lo} {hi}" (randNat h lo hi == randNatRef h lo hi)
    check s!"split agrees on {repr h}" (split h == splitRef h)
    let x := (randNat h lo hi).1
    check s!"randNat {lo} {hi} in range" (min lo hi ≤ x && x ≤ max lo hi)

def edgeCases (check : String → Bool → IO Unit) : IO Unit := do
  -- Seed from IO so the generator isn't a compile-time constant.
  let g ← newIO
  -- `g` is used again afterwards, so C must not update it in place.
  -- `lazyPure` keeps the calls in order and stops them being merged.
  let r ← IO.lazyPure fun _ => randNat g 0 1000
  let s ← IO.lazyPure fun _ => split g
  check "shared randNat leaves generator intact" (r == (← IO.lazyPure fun _ => randNatRef g 0 1000))
  check "shared split leaves generator intact" (s == (← IO.lazyPure fun _ => splitRef g))
  let max63 := 2 ^ 63 - 1
  -- Largest unboxed bounds, and the smallest ones that aren't.
  for (lo, hi) in [(0, max63), (max63, 0), (max63, max63), (0, 2 ^ 63), (2 ^ 63, 2 ^ 63),
                   (0, 2 ^ 64 - 1), (0, 2 ^ 64), (2 ^ 64, 2 ^ 64 + 1)] do
    check s!"edge {lo} {hi}" (randNat g lo hi == randNatRef g lo hi)
  check "empty range consumes nothing" (randNat g 5 5 == (5, g))

/-- Pearson's chi-squared statistic for `n` draws into `k` buckets. -/
def chiSquared (k n : Nat) (draw : SplitMix → Nat × SplitMix) (g : SplitMix) : Float := Id.run do
  let mut counts := Array.replicate k 0
  let mut g := g
  for _ in [0:n] do
    let (x, g') := draw g; g := g'
    counts := counts.modify x (· + 1)
  let expected := n.toFloat / k.toFloat
  return counts.foldl (fun acc c => acc + (c.toFloat - expected) ^ 2 / expected) 0

def uniformity (check : String → Bool → IO Unit) : IO Unit := do
  -- 99.9% critical values of the chi-squared distribution; seeds are fixed,
  -- so these can't flake.
  let g := ofSeed 2026
  check "uniform 0..9" (chiSquared 10 100000 (randNat · 0 9) g < 27.88)
  check "uniform 0..4 (most rejections)" (chiSquared 5 100000 (randNat · 0 4) g < 18.47)
  -- Bignum range: which of three 2^64-wide bands a draw lands in.
  let bands := fun g => let (x, g) := randNat g 0 (3 * 2 ^ 64 - 1); (x / 2 ^ 64, g)
  check "uniform bignum bands" (chiSquared 3 30000 bands g < 13.82)

def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  let check := check failures
  agreement check
  edgeCases check
  uniformity check
  let n ← failures.get
  if n == 0 then
    IO.println "All tests passed."
    return 0
  IO.eprintln s!"{n} checks failed."
  return 1
