import Mvc.Checker

/-! Small end-to-end controls, including rejection of a sharp equality.
All executable acceptance/rejection facts below use kernel `decide`.
-/
namespace Mvc.CheckerControls

def cubicCenters : List RationalComplex := [⟨1, 0, 1⟩, ⟨-1, 0, 1⟩]

theorem cubic_half_accepts : Computation.check 16 cubicCenters 1 2 = true := by decide

theorem cubic_sharp_rejects : Computation.check 16 cubicCenters 2 3 = false := by decide

theorem zero_center_rejects : Computation.check 16 [⟨0, 0, 1⟩] 1 2 = false := by decide

theorem zero_denominator_rejects : Computation.check 16 cubicCenters 1 0 = false := by decide

theorem cubic_half_bound :
    CriticalBound (prescribedPolynomial (cubicCenters.map RationalComplex.value)) (1/2) := by
  simpa using check_sound cubic_half_accepts

theorem cubic_degree :
    (prescribedPolynomial (cubicCenters.map RationalComplex.value)).natDegree = 3 := by
  simpa [cubicCenters] using (check_sound_full cubic_half_accepts).1

end Mvc.CheckerControls
