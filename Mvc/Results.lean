import Mvc.Witnesses.Degree2650
import Mvc.Witnesses.Degree2725
import Mvc.Witnesses.Degree2798
import Mvc.Witnesses.Degree2840
import Mvc.Witnesses.Degree2917

/-! The four public results. `N` is polynomial degree; the historical bound is
`(N - 1) / N`, equivalently `d / (d + 1)` when `d = N - 1`.
The two named polynomials are explicit witnesses, not global minimality results.
-/
namespace Mvc.Results

/-- Every exact degree N≥2650 admits a degree-dependent MVC counterexample. -/
theorem every_degree_ge_2650 (N : ℕ) (hN : 2650 ≤ N) :
    ∃ P : Polynomial ℂ, P.natDegree = N ∧ P.eval 0 = 0 ∧
      P.derivative.eval 0 = 1 ∧
      ∀ c : ℂ, P.derivative.eval c = 0 →
        ((N : ℝ) - 1) / (N : ℝ) < ‖P.eval c / c‖ :=
  degree_bound_all_ge_2650 Witnesses.degree2650_witness Witnesses.degree2725_witness
    Witnesses.degree2798_witness Witnesses.degree2840_witness
    Witnesses.degree2917_witness hN

/-- Every exact degree N≥2917 admits a constant-one MVC counterexample. -/
theorem every_degree_ge_2917 (N : ℕ) (hN : 2917 ≤ N) :
    ∃ P : Polynomial ℂ, P.natDegree = N ∧ P.eval 0 = 0 ∧
      P.derivative.eval 0 = 1 ∧
      ∀ c : ℂ, P.derivative.eval c = 0 → 1 < ‖P.eval c / c‖ :=
  ordinary_all_ge_2917 Witnesses.degree2917_witness hN

/-- Our explicit degree-2650 polynomial beats 2649/2650 at every critical point. -/
theorem explicit_degree_2650 :
    Witnesses.polynomial2650.natDegree = 2650 ∧
    Witnesses.polynomial2650.eval 0 = 0 ∧
    Witnesses.polynomial2650.derivative.eval 0 = 1 ∧
    ∀ c : ℂ, Witnesses.polynomial2650.derivative.eval c = 0 →
      (2649 : ℝ) / 2650 < ‖Witnesses.polynomial2650.eval c / c‖ := by
  obtain ⟨hdeg,h0,h1,hc⟩ := Witnesses.degree2650_explicit
  refine ⟨hdeg,h0,h1,?_⟩
  intro c h
  exact lt_trans (by norm_num : (2649:ℝ)/2650 < 99964059/100000000) (hc c h)

/-- Our explicit degree-2917 polynomial beats one at every critical point. -/
theorem explicit_degree_2917 :
    Witnesses.polynomial2917.natDegree = 2917 ∧
    Witnesses.polynomial2917.eval 0 = 0 ∧
    Witnesses.polynomial2917.derivative.eval 0 = 1 ∧
    ∀ c : ℂ, Witnesses.polynomial2917.derivative.eval c = 0 →
      1 < ‖Witnesses.polynomial2917.eval c / c‖ := by
  obtain ⟨hdeg,h0,h1,hc⟩ := Witnesses.degree2917_explicit
  refine ⟨hdeg,h0,h1,?_⟩
  intro c h
  exact lt_trans (by norm_num : (1:ℝ) < 1000000129/1000000000) (hc c h)

end Mvc.Results
