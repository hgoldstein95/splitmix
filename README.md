# splitmix

SplitMix64 for Lean 4, implemented in C, bit-for-bit compatible with Haskell's
[`splitmix`](https://hackage.haskell.org/package/splitmix) package.

```lean
import SplitMix

SplitMix.ofSeed : UInt64 → SplitMix                     -- Haskell `mkSMGen`
SplitMix.newIO  : IO SplitMix                           -- seeded from system entropy
SplitMix.split  : SplitMix → SplitMix × SplitMix         -- Haskell `splitSMGen`
SplitMix.randNat : SplitMix → Nat → Nat → Nat × SplitMix -- inclusive, either order; Haskell `nextInteger`

-- A mutable generator, updated in place: the fast path for drawing repeatedly.
SplitMix.Gen.new        : SplitMix → BaseIO SplitMix.Gen
SplitMix.Gen.get        : SplitMix.Gen → BaseIO SplitMix
SplitMix.Gen.set        : SplitMix.Gen → SplitMix → BaseIO Unit
SplitMix.Gen.randNat    : SplitMix.Gen → (lo hi : Nat) → BaseIO {x // min lo hi ≤ x ∧ x ≤ max lo hi}
SplitMix.Gen.nextUInt64 : SplitMix.Gen → BaseIO UInt64
SplitMix.Gen.split      : SplitMix.Gen → BaseIO SplitMix.Gen

theorem SplitMix.randNat_mem (h : lo ≤ hi) : lo ≤ (randNat g lo hi).1 ∧ (randNat g lo hi).1 ≤ hi
```

## Caveats

- The Lean bodies are only for proofs. The interpreter always calls the C.
- Inside hot loops, don't write `Nat` literals of 2^32 or more inline: Lean
  compiles them to a string parse on every call. Bind them once outside.

## Development

```sh
lake test                          # C vs spec, edge cases, uniformity
lake exe bench                     # against the Lean spec and core StdGen
(cd test/downstream && lake build) # #eval and linking from a dependent package
```
