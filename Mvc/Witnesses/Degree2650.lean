import Mvc.Certificate
import Mvc.Data.Degree2650

/-! Concrete Lean proof for the exact degree-2650 polynomial.
The arithmetic acceptance is computed in Lean, not imported from another checker.
native_decide adds Lean's compiler/runtime to the trusted computing base.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Mvc.Witnesses

noncomputable def polynomial2650 : Polynomial ℂ :=
  prescribedPolynomial (Data.degree2650.map RationalComplex.value)

theorem degree2650_accepts :
    Computation.check 16000 Data.degree2650 99964059 100000000 = true := by
  native_decide

theorem degree2650_length : Data.degree2650.length + 1 = 2650 := by
  decide

theorem degree2650_explicit :
    polynomial2650.natDegree = 2650 ∧
    polynomial2650.eval 0 = 0 ∧
    polynomial2650.derivative.eval 0 = 1 ∧
    CriticalBound polynomial2650 ((99964059 : ℝ) / 100000000) := by
  have h := check_sound_full degree2650_accepts
  simpa only [polynomial2650, degree2650_length] using h

theorem degree2650_witness :
    HasWitness 2650 ((99964059 : ℝ) / 100000000) :=
  ⟨polynomial2650, degree2650_explicit⟩

end Mvc.Witnesses

