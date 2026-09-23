# splitmix

SplitMix64 for Lean 4, implemented in C, bit-for-bit compatible with
Haskell's [`splitmix`](https://hackage.haskell.org/package/splitmix) package.

```lean
import SplitMix

SplitMix.ofSeed : UInt64 → SplitMix                     -- Haskell `mkSMGen`
SplitMix.newIO  : IO SplitMix                           -- seeded from system entropy
SplitMix.split  : SplitMix → SplitMix × SplitMix         -- Haskell `splitSMGen`
SplitMix.randNat : SplitMix → Nat → Nat → Nat × SplitMix -- inclusive, either order; Haskell `nextInteger`

theorem SplitMix.randNat_mem (h : lo ≤ hi) : lo ≤ (randNat g lo hi).1 ∧ (randNat g lo hi).1 ≤ hi
```

Add it to a Lake package with `require splitmix from git "<url>"`.

## How it's put together

- `SplitMix/Native.lean` gives every operation a pure Lean definition (the
  spec, which proofs use) and marks it `@[extern]`, so compiled code calls
  `c/splitmix.c` instead.
- The C handles bounds below 2^63 without allocating per draw, and reuses the
  generator's memory when it's unshared. Larger bounds call back into the Lean
  spec through an `@[export]`ed function.
- `SplitMix.Native` is in its own precompiled library, `SplitMixFFI`, so
  `#eval` can find the native code in this package and in its dependents. It
  must stay declared after `SplitMix` in `lakefile.lean`.

## Caveats

- A file that declares `@[extern]` functions can't `#eval` them itself, and
  `lake env lean File.lean` can't either. `lake build`, `lake lean` and the
  editor all work.
- The Lean bodies are only for proofs. The interpreter always calls the C.
- Inside hot loops, don't write `Nat` literals of 2^32 or more inline: Lean
  compiles them to a string parse on every call. Bind them once outside.

## Development

```sh
lake test                          # C vs spec, edge cases, uniformity
lake exe bench                     # against the Lean spec and core StdGen
(cd test/downstream && lake build) # #eval and linking from a dependent package
```
