import Mvc.Checker
import Mvc.Coverage

/-!
# Packaging a checked exact polynomial as an MVC witness

These theorems do not assert acceptance of a particular numerical data set.
The Boolean acceptance and the concrete list length must both be supplied.
-/

namespace Mvc

/-- A successful arithmetic check supplies the exact-degree normalized witness. -/
theorem hasWitness_of_check {bits : Nat} {cs : List RationalComplex}
    {num den N : Nat} (hcheck : Computation.check bits cs num den = true)
    (hlen : cs.length + 1 = N) :
    HasWitness N ((num : ℝ) / (den : ℝ)) := by
  obtain ⟨hdeg, hzero, hone, hbound⟩ := check_sound_full hcheck
  refine ⟨prescribedPolynomial (cs.map RationalComplex.value), ?_, hzero, hone, hbound⟩
  exact hdeg.trans hlen

/-- Equivalent packaging when the center count is specified as `N - 1`. -/
theorem hasWitness_of_check_length_sub_one {bits : Nat} {cs : List RationalComplex}
    {num den N : Nat} (hcheck : Computation.check bits cs num den = true)
    (hN : 2 ≤ N) (hlen : cs.length = N - 1) :
    HasWitness N ((num : ℝ) / (den : ℝ)) := by
  apply hasWitness_of_check hcheck
  omega

end Mvc
