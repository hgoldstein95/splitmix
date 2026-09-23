import SplitMix

def main : IO Unit := do
  let (a, b) := SplitMix.split (← SplitMix.newIO)
  IO.println s!"{(SplitMix.randNat a 1 6).1} {(SplitMix.randNat b 0 (2 ^ 100)).1}"
