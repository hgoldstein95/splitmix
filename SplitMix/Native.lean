/-!
# SplitMix64: specification and native bindings

A port of Haskell's `splitmix` package (`System.Random.SplitMix`).  Each operation has a pure Lean
definition that proofs can consume. Compiled code calls the C implementation in `c/splitmix.c`
instead.

This is the only module with `@[extern]`/`@[export]` declarations. It lives in the precompiled
`SplitMixFFI` library so the interpreter (`#eval`, elaboration time code) can find the native
symbols.
-/

/-- A SplitMix64 generator: a 64-bit state `seed` that advances by the odd
constant `gamma` on each draw. Build one with `SplitMix.ofSeed` or
`SplitMix.newIO`. -/
structure SplitMix where
  seed : UInt64
  gamma : UInt64
  deriving Repr, DecidableEq

namespace SplitMix

/-- Murmur3 finalizer (Haskell `mix64`). -/
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 33)) * 0xff51afd7ed558ccd
  let z := (z ^^^ (z >>> 33)) * 0xc4ceb9fe1a85ec53
  z ^^^ (z >>> 33)

/-- Stafford variant 13 (Haskell `mix64variant13`). -/
def mix64Variant13 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- Number of set bits. -/
def popCount (z : UInt64) : Nat :=
  (List.range 64).countP fun i => (z >>> i.toUInt64) &&& 1 == 1

/-- Haskell `mixGamma`: an odd gamma with at least 24 bit transitions. -/
def mixGamma (z : UInt64) : UInt64 :=
  let z := mix64Variant13 z ||| 1
  if popCount (z ^^^ (z >>> 1)) ≥ 24 then z else z ^^^ 0xaaaaaaaaaaaaaaaa

/-- The golden-ratio gamma, `⌊2^64 / φ⌋` rounded to odd. -/
def goldenGamma : UInt64 := 0x9e3779b97f4a7c15

/-- Build a generator from a seed (Haskell `mkSMGen`). -/
def ofSeed (s : UInt64) : SplitMix :=
  ⟨mix64 s, mixGamma (s + goldenGamma)⟩

instance : Inhabited SplitMix := ⟨ofSeed 0⟩

/-- Draw 64 uniformly random bits (Haskell `nextWord64`). -/
def nextUInt64 (g : SplitMix) : UInt64 × SplitMix :=
  let seed := g.seed + g.gamma
  (mix64 seed, { g with seed })

/-- Specification of `split` (Haskell `splitSMGen`). -/
def splitRef (g : SplitMix) : SplitMix × SplitMix :=
  let s1 := g.seed + g.gamma
  let s2 := s1 + g.gamma
  (⟨s2, g.gamma⟩, ⟨mix64 s1, mixGamma s2⟩)

/-- For `range > 0`: the mask for the most significant 64-bit digit of
`range`, and the number of digits below it. -/
def rangeShape (range : Nat) : UInt64 × Nat :=
  let rest := range.log2 / 64
  let top := range >>> (64 * rest)
  ((2 ^ (top.log2 + 1) - 1 : Nat).toUInt64, rest)

/-- Draw a candidate: one masked leading digit, then `rest` full digits,
most significant first. -/
def drawDigits (mask : UInt64) (rest : Nat) (g : SplitMix) : Nat × SplitMix :=
  let (x, g) := g.nextUInt64
  go (x &&& mask).toNat rest g
where
  go (acc : Nat) : Nat → SplitMix → Nat × SplitMix
    | 0, g => (acc, g)
    | n + 1, g =>
      let (x, g) := g.nextUInt64
      go ((acc <<< 64) ||| x.toNat) n g

/-- Rejection loop. `fuel` exists only to make this a total function: with
the `2^64` that `boundedRef` passes, it cannot run out for `range < 2^64`
and practically never runs out otherwise. -/
def boundedLoop (range : Nat) (mask : UInt64) (rest : Nat) : Nat → SplitMix → Nat × SplitMix
  | 0, g => (0, g)
  | fuel + 1, g =>
    let (x, g) := drawDigits mask rest g
    if x ≤ range then (x, g) else boundedLoop range mask rest fuel g

/-- A uniform `Nat` in `[0, range]`, for `range > 0` (Haskell `nextInteger'`). -/
def boundedRef (range : Nat) (g : SplitMix) : Nat × SplitMix :=
  let (mask, rest) := rangeShape range
  boundedLoop range mask rest (2 ^ 64) g

/-- Specification of `randNat` (Haskell `nextInteger`). -/
def randNatRef (g : SplitMix) (lo hi : Nat) : Nat × SplitMix :=
  if lo < hi then
    let (i, g) := boundedRef (hi - lo) g
    (lo + i, g)
  else if hi < lo then
    let (i, g) := boundedRef (lo - hi) g
    (hi + i, g)
  else
    (lo, g)

/-- Called from C when a bound is too big for its fast path. -/
@[export lean_splitmix_rand_nat_slow]
private def randNatSlow (g : SplitMix) (lo hi : Nat) : Nat × SplitMix :=
  randNatRef g lo hi

/-- Split a generator into two independent generators. -/
@[extern "lean_splitmix_split"]
def split (g : SplitMix) : SplitMix × SplitMix :=
  splitRef g

/-- A uniformly random `Nat` between `lo` and `hi`, inclusive. The bounds may
be given in either order. -/
@[extern "lean_splitmix_rand_nat"]
def randNat (g : SplitMix) (lo hi : Nat) : Nat × SplitMix :=
  randNatRef g lo hi


/-! ## Mutable generators

`SplitMix.Gen` is a generator that is updated in place: a C object holding a `seed` and a `gamma`.
It draws exactly what the pure functions above draw, but a draw allocates nothing and touches no
reference counts, so it is the fast path for code that keeps one generator and draws from it
repeatedly (a random-testing loop, for instance).

The operations are `opaque`: Lean knows only their types. Their meaning is the pure `SplitMix`
functions, and the tests check that they agree with them: `g.randNat lo hi` is `randNatRef` on the
generator `g.get` returns, leaving `g` holding the generator `randNatRef` returns, and likewise for
`nextUInt64` and `split`.

A `Gen` is not thread-safe: two tasks must not use the same one at the same time.
-/

private opaque GenPointed : NonemptyType

/-- A mutable SplitMix64 generator. Make one with `Gen.new`. -/
def Gen : Type := GenPointed.type

instance : Nonempty Gen := GenPointed.property

/-- A mutable generator starting from `g`. -/
@[extern "lean_splitmix_gen_new"]
opaque Gen.new (g : @& SplitMix) : BaseIO Gen

/-- The generator's current state, as a pure value. -/
@[extern "lean_splitmix_gen_get"]
opaque Gen.get (g : @& Gen) : BaseIO SplitMix

/-- Replace the generator's state (to reseed it, for instance). -/
@[extern "lean_splitmix_gen_set"]
opaque Gen.set (g : @& Gen) (s : @& SplitMix) : BaseIO Unit

/-- Draw 64 uniformly random bits (Haskell `nextWord64`). Spec: `nextUInt64`. -/
@[extern "lean_splitmix_gen_next_uint64"]
opaque Gen.nextUInt64 (g : @& Gen) : BaseIO UInt64

/-- A uniformly random `Nat` between `lo` and `hi`, inclusive; the bounds may be given in either
order. Spec: `randNatRef`. Bounds below 2^63 take the C fast path, which allocates nothing. -/
@[extern "lean_splitmix_gen_rand_nat"]
opaque Gen.randNat (g : @& Gen) (lo hi : @& Nat) :
    BaseIO {x : Nat // min lo hi ≤ x ∧ x ≤ max lo hi} :=
  pure ⟨min lo hi, Nat.le_refl _, by omega⟩

/-- Split off an independent generator: `g` advances to the first half of `splitRef` and the
result starts from the second. Spec: `splitRef`. -/
@[extern "lean_splitmix_gen_split"]
opaque Gen.split (g : @& Gen) : BaseIO Gen

end SplitMix
