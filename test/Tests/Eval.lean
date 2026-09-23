import SplitMix

/-! These run in the interpreter while this file is elaborated, so a build
failure here means `#eval` can't find the native code, or the C disagrees
with the Lean spec. -/

open SplitMix

-- C fast path.
#guard randNat (ofSeed 0) 0 9 == randNatRef (ofSeed 0) 0 9
#guard randNat (ofSeed 0) 9 0 == randNatRef (ofSeed 0) 9 0
-- C falling back to Lean for a bignum range.
#guard randNat (ofSeed 0) (3 ^ 50) (7 ^ 40) == randNatRef (ofSeed 0) (3 ^ 50) (7 ^ 40)
#guard split (ofSeed 0) == splitRef (ofSeed 0)
