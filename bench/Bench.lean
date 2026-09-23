import SplitMix

/-! `lake exe bench`: SplitMix (C) against the pure-Lean spec and Lean's
built-in `StdGen`. -/

@[specialize]
def drawLoop {γ} (next : γ → Nat × γ) : Nat → γ → Nat → Nat
  | 0, _, acc => acc
  | k + 1, g, acc => let (x, g) := next g; drawLoop next k g (acc ^^^ x)

/-- Alternates halves so neither side of the split is dead code. -/
@[specialize]
def splitLoop {γ} (split : γ → γ × γ) : Nat → γ → γ
  | 0, g => g
  | k + 1, g => let (a, b) := split g; splitLoop split k (if k % 2 == 0 then a else b)

/-- Bounds are computed once here. Written inline, `Nat` literals of 2^32 or
more compile to `lean_cstr_to_nat("…")` and get re-parsed on every call. -/
@[noinline] def pow2 (k : Nat) : Nat := 2 ^ k

/-- `n` draws from one mutable generator. -/
def genLoop (gen : SplitMix.Gen) (lo hi : Nat) : Nat → Nat → BaseIO Nat
  | 0, acc => pure acc
  | k + 1, acc => do genLoop gen lo hi k (acc ^^^ (← gen.randNat lo hi).1)

def time (label : String) (n : Nat) (act : Unit → IO String) : IO Unit := do
  let start ← IO.monoNanosNow
  let result ← act ()
  let stop ← IO.monoNanosNow
  let tenths := (stop - start) * 10 / n
  IO.println s!"{label.pushn ' ' (36 - label.length)}{tenths / 10}.{tenths % 10} ns/op   ({result.take 20})"

def main : IO Unit := do
  let n := 10000000
  let sm := SplitMix.ofSeed 42
  let std := mkStdGen 42
  IO.println s!"{n} operations each\n"
  time "randNat 0..999      SplitMix (C)" n fun _ =>
    return toString (drawLoop (SplitMix.randNat · 0 999) n sm 0)
  time "randNat 0..999      Gen (C)" n fun _ => do
    return toString (← genLoop (← SplitMix.Gen.new sm) 0 999 n 0)
  time "randNat 0..999      Lean spec" n fun _ =>
    return toString (drawLoop (SplitMix.randNatRef · 0 999) n sm 0)
  time "randNat 0..999      StdGen" n fun _ =>
    return toString (drawLoop (randNat · 0 999) n std 0)
  time "randNat 0..2^62     SplitMix (C)" n fun _ =>
    return toString (drawLoop (SplitMix.randNat · 0 (pow2 62)) n sm 0)
  time "randNat 0..2^62     StdGen" n fun _ =>
    return toString (drawLoop (randNat · 0 (pow2 62)) n std 0)
  time "randNat 0..2^100    SplitMix (Lean)" (n / 10) fun _ =>
    return toString (drawLoop (SplitMix.randNat · 0 (pow2 100)) (n / 10) sm 0)
  time "randNat 0..2^100    StdGen" (n / 10) fun _ =>
    return toString (drawLoop (randNat · 0 (pow2 100)) (n / 10) std 0)
  time "split               SplitMix (C)" n fun _ =>
    return toString (repr (splitLoop SplitMix.split n sm))
  time "split               Lean spec" n fun _ =>
    return toString (repr (splitLoop SplitMix.splitRef n sm))
  time "split               StdGen" n fun _ =>
    return toString (repr (splitLoop stdSplit n std))
