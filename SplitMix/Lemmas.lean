import SplitMix.Native

/-! Every `randNat` result lies between its bounds. -/

namespace SplitMix

theorem boundedRef_le (range : Nat) (g : SplitMix) : (boundedRef range g).1 ≤ range :=
  (boundedLoop ..).1.property

theorem randNat_ge_min (g : SplitMix) (lo hi : Nat) : min lo hi ≤ (randNat g lo hi).1 := by
  simp only [randNat, randNatRef]
  split
  · simp; omega
  · split <;> simp <;> omega

theorem randNat_le_max (g : SplitMix) (lo hi : Nat) : (randNat g lo hi).1 ≤ max lo hi := by
  simp only [randNat, randNatRef]
  split
  · have := boundedRef_le (hi - lo) g; simp; omega
  · split
    · have := boundedRef_le (lo - hi) g; simp; omega
    · simp; omega

theorem randNat_mem {lo hi : Nat} (g : SplitMix) (h : lo ≤ hi) :
    lo ≤ (randNat g lo hi).1 ∧ (randNat g lo hi).1 ≤ hi := by
  have := randNat_ge_min g lo hi
  have := randNat_le_max g lo hi
  omega

end SplitMix
