import Mvc.Certificate
import Mvc.Data.Degree2725

/-! Concrete Lean proof for the exact degree-2725 polynomial.
The arithmetic acceptance is computed in Lean, not imported from another checker.
native_decide adds Lean's compiler/runtime to the trusted computing base.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Mvc.Witnesses

noncomputable def polynomial2725 : Polynomial ℂ :=
  prescribedPolynomial (Data.degree2725.map RationalComplex.value)

theorem degree2725_accepts :
    Computation.check 16000 Data.degree2725 9996431 10000000 = true := by
  native_decide

theorem degree2725_length : Data.degree2725.length + 1 = 2725 := by
  decide

theorem degree2725_explicit :
    polynomial2725.natDegree = 2725 ∧
    polynomial2725.eval 0 = 0 ∧
    polynomial2725.derivative.eval 0 = 1 ∧
    CriticalBound polynomial2725 ((9996431 : ℝ) / 10000000) := by
  have h := check_sound_full degree2725_accepts
  simpa only [polynomial2725, degree2725_length] using h

theorem degree2725_witness :
    HasWitness 2725 ((9996431 : ℝ) / 10000000) :=
  ⟨polynomial2725, degree2725_explicit⟩

end Mvc.Witnesses

