import SplitMix.Native

namespace SplitMix

/-- A generator seeded from system entropy. -/
def newIO : IO SplitMix := do
  return ofSeed (← IO.getRandomBytes 8).toUInt64LE!

end SplitMix
