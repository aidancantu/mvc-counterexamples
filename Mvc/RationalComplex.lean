import Mvc.ComplexBox

namespace Mvc

/-- Exact complex rational coordinates with one common positive denominator. -/
structure RationalComplex where
  re : Int
  im : Int
  den : Nat
  deriving DecidableEq, Repr

namespace RationalComplex

noncomputable def value (c : RationalComplex) : ℂ :=
  ⟨(c.re:ℝ)/(c.den:ℝ), (c.im:ℝ)/(c.den:ℝ)⟩

def box (s : Nat) (c : RationalComplex) : ComplexBox :=
  ComplexBox.ofFrac s c.re c.im c.den

def valid (c : RationalComplex) : Bool :=
  decide (0 < c.den ∧ (c.re ≠ 0 ∨ c.im ≠ 0))

theorem valid_pos {c : RationalComplex} (h : c.valid = true) : 0 < c.den := by
  have hh : 0 < c.den ∧ (c.re ≠ 0 ∨ c.im ≠ 0) := by simpa [valid] using h
  exact hh.1

theorem valid_ne_zero {c : RationalComplex} (h : c.valid = true) : c.value ≠ 0 := by
  have hh : 0 < c.den ∧ (c.re ≠ 0 ∨ c.im ≠ 0) := by simpa [valid] using h
  have hd : (c.den:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh.1
  intro hz
  have hr : (c.re:ℝ)/(c.den:ℝ) = 0 := congrArg Complex.re hz
  have hi : (c.im:ℝ)/(c.den:ℝ) = 0 := congrArg Complex.im hz
  have hr0 : c.re = 0 := by exact_mod_cast ((div_eq_zero_iff).mp hr).resolve_right hd
  have hi0 : c.im = 0 := by exact_mod_cast ((div_eq_zero_iff).mp hi).resolve_right hd
  rcases hh.2 with h | h
  · exact h hr0
  · exact h hi0

theorem box_contains (s : Nat) (c : RationalComplex) (hd : 0 < c.den) :
    (c.box s).Contains s c.value :=
  ComplexBox.contains_ofFrac s c.re c.im hd

end RationalComplex

namespace ComplexBox

/-- Multiply a rectangular enclosure by a small exact rational point.
No multiplication of two full-precision integer endpoints is needed. -/
def mulExact (a : ComplexBox) (c : RationalComplex) : ComplexBox :=
  ⟨(Interval.mulFrac a.re c.re c.den).sub (Interval.mulFrac a.im c.im c.den),
   (Interval.mulFrac a.re c.im c.den).add (Interval.mulFrac a.im c.re c.den)⟩

theorem contains_mulExact {s : Nat} {a : ComplexBox} {z : ℂ}
    (hz : Contains s a z) (c : RationalComplex) (hd : 0 < c.den) :
    Contains s (mulExact a c) (z*c.value) := by
  exact ⟨Interval.contains_sub (Interval.contains_mulFrac hz.1 c.re hd)
      (Interval.contains_mulFrac hz.2 c.im hd),
    Interval.contains_add (Interval.contains_mulFrac hz.1 c.im hd)
      (Interval.contains_mulFrac hz.2 c.re hd)⟩

end ComplexBox
end Mvc
