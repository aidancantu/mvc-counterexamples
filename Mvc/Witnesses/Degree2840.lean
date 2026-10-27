import Mvc.Certificate
import Mvc.Data.Degree2840

/-! Concrete Lean proof for the exact degree-2840 polynomial.
The arithmetic acceptance is computed in Lean, not imported from another checker.
native_decide adds Lean's compiler/runtime to the trusted computing base.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Mvc.Witnesses

noncomputable def polynomial2840 : Polynomial ℂ :=
  prescribedPolynomial (Data.degree2840.map RationalComplex.value)

theorem degree2840_accepts :
    Computation.check 16000 Data.degree2840 249917 250000 = true := by
  native_decide

theorem degree2840_length : Data.degree2840.length + 1 = 2840 := by
  decide

theorem degree2840_explicit :
    polynomial2840.natDegree = 2840 ∧
    polynomial2840.eval 0 = 0 ∧
    polynomial2840.derivative.eval 0 = 1 ∧
    CriticalBound polynomial2840 ((249917 : ℝ) / 250000) := by
  have h := check_sound_full degree2840_accepts
  simpa only [polynomial2840, degree2840_length] using h

theorem degree2840_witness :
    HasWitness 2840 ((249917 : ℝ) / 250000) :=
  ⟨polynomial2840, degree2840_explicit⟩

end Mvc.Witnesses

