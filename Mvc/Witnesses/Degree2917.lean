import Mvc.Certificate
import Mvc.Data.Degree2917

/-! Concrete Lean proof for the exact degree-2917 polynomial.
The arithmetic acceptance is computed in Lean, not imported from another checker.
native_decide adds Lean's compiler/runtime to the trusted computing base.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Mvc.Witnesses

noncomputable def polynomial2917 : Polynomial ℂ :=
  prescribedPolynomial (Data.degree2917.map RationalComplex.value)

theorem degree2917_accepts :
    Computation.check 16000 Data.degree2917 1000000129 1000000000 = true := by
  native_decide

theorem degree2917_length : Data.degree2917.length + 1 = 2917 := by
  decide

theorem degree2917_explicit :
    polynomial2917.natDegree = 2917 ∧
    polynomial2917.eval 0 = 0 ∧
    polynomial2917.derivative.eval 0 = 1 ∧
    CriticalBound polynomial2917 ((1000000129 : ℝ) / 1000000000) := by
  have h := check_sound_full degree2917_accepts
  simpa only [polynomial2917, degree2917_length] using h

theorem degree2917_witness :
    HasWitness 2917 ((1000000129 : ℝ) / 1000000000) :=
  ⟨polynomial2917, degree2917_explicit⟩

end Mvc.Witnesses

