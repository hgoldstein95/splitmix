import SplitMix

open SplitMix

#guard randNat (ofSeed 0) 0 9 == randNatRef (ofSeed 0) 0 9
#guard randNat (ofSeed 0) (3 ^ 50) (7 ^ 40) == randNatRef (ofSeed 0) (3 ^ 50) (7 ^ 40)
#eval do
  let g ← newIO
  let (a, b) := split g
  return ((randNat a 1 6).1, (randNat b 1 6).1)
