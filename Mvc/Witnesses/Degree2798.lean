import Mvc.Certificate
import Mvc.Data.Degree2798

/-! Concrete Lean proof for the exact degree-2798 polynomial.
The arithmetic acceptance is computed in Lean, not imported from another checker.
native_decide adds Lean's compiler/runtime to the trusted computing base.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Mvc.Witnesses

noncomputable def polynomial2798 : Polynomial ℂ :=
  prescribedPolynomial (Data.degree2798.map RationalComplex.value)

theorem degree2798_accepts :
    Computation.check 16000 Data.degree2798 999649 1000000 = true := by
  native_decide

theorem degree2798_length : Data.degree2798.length + 1 = 2798 := by
  decide

theorem degree2798_explicit :
    polynomial2798.natDegree = 2798 ∧
    polynomial2798.eval 0 = 0 ∧
    polynomial2798.derivative.eval 0 = 1 ∧
    CriticalBound polynomial2798 ((999649 : ℝ) / 1000000) := by
  have h := check_sound_full degree2798_accepts
  simpa only [polynomial2798, degree2798_length] using h

theorem degree2798_witness :
    HasWitness 2798 ((999649 : ℝ) / 1000000) :=
  ⟨polynomial2798, degree2798_explicit⟩

end Mvc.Witnesses

