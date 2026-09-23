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
-- `Gen`, from the interpreter: the C fast path, the Lean fallback and `split`.
#eval show IO Unit from do
  let gen ← Gen.new (ofSeed 0)
  let x ← gen.randNat 0 9
  let (y, g) := randNatRef (ofSeed 0) 0 9
  unless x.1 == y && (← gen.get) == g do throw (IO.userError "Gen.randNat disagrees with randNatRef")
  let x ← gen.randNat (3 ^ 50) (7 ^ 40)
  let (y, g) := randNatRef g (3 ^ 50) (7 ^ 40)
  unless x.1 == y && (← gen.get) == g do
    throw (IO.userError "Gen.randNat disagrees with randNatRef on a bignum range")
  let other ← gen.split
  unless (← gen.get, ← other.get) == splitRef g do throw (IO.userError "Gen.split disagrees with splitRef")
