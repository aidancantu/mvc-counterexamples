import Mvc.Polynomial

/-!
# Executable ascending coefficient lists

These recursive functions mirror the numerical certificate computation, while
all semantic identities below are proved in Lean.
-/

noncomputable section

open Polynomial

namespace Mvc

/-- A list of ascending coefficients interpreted as a complex polynomial. -/
def ofCoeffs : List ℂ → ℂ[X]
  | [] => 0
  | a :: as => C a + X * ofCoeffs as

/-- Multiply an ascending coefficient list by `X - C c`, carrying the previous
coefficient from one position to the next. -/
def mulLinearAux (c : ℂ) : ℂ → List ℂ → List ℂ
  | prev, [] => [prev]
  | prev, a :: as => (prev - c * a) :: mulLinearAux c a as

/-- Ascending coefficients of the monic critical product. -/
def productCoeffs : List ℂ → List ℂ
  | [] => [1]
  | c :: cs => mulLinearAux c 0 (productCoeffs cs)

/-- Divide successive coefficients by the successive positive integers. -/
def integrateAux : ℕ → List ℂ → List ℂ
  | _, [] => []
  | k, a :: as => (a / ((k + 1 : ℕ) : ℂ)) :: integrateAux (k + 1) as

/-- Horner evaluation of ascending coefficients. -/
def evalCoeffs : List ℂ → ℂ → ℂ
  | [], _ => 0
  | a :: as, z => a + z * evalCoeffs as z

 theorem ofCoeffs_mulLinearAux (c prev : ℂ) (as : List ℂ) :
    ofCoeffs (mulLinearAux c prev as) = C prev + (X - C c) * ofCoeffs as := by
  induction as generalizing prev with
  | nil => simp [mulLinearAux, ofCoeffs]
  | cons a as ih =>
    simp only [mulLinearAux, ofCoeffs, ih, map_sub, map_mul]
    ring

 theorem ofCoeffs_productCoeffs (cs : List ℂ) :
    ofCoeffs (productCoeffs cs) = criticalProduct cs := by
  induction cs with
  | nil => simp [productCoeffs, ofCoeffs, criticalProduct]
  | cons c cs ih =>
    simp [productCoeffs, ofCoeffs_mulLinearAux, criticalProduct, ih]

 theorem eval_ofCoeffs (as : List ℂ) (z : ℂ) :
    (ofCoeffs as).eval z = evalCoeffs as z := by
  induction as with
  | nil => simp [ofCoeffs, evalCoeffs]
  | cons a as ih => simp [ofCoeffs, evalCoeffs, ih]

 theorem length_mulLinearAux (c prev : ℂ) (as : List ℂ) :
    (mulLinearAux c prev as).length = as.length + 1 := by
  induction as generalizing prev with
  | nil => simp [mulLinearAux]
  | cons a as ih => simp [mulLinearAux, ih]

 theorem length_productCoeffs (cs : List ℂ) :
    (productCoeffs cs).length = cs.length + 1 := by
  induction cs with
  | nil => simp [productCoeffs]
  | cons c cs ih => simp [productCoeffs, length_mulLinearAux, ih]

 theorem length_integrateAux (k : ℕ) (as : List ℂ) :
    (integrateAux k as).length = as.length := by
  induction as generalizing k with
  | nil => simp [integrateAux]
  | cons a as ih => simp [integrateAux, ih]

 theorem derivative_shifted_integrateAux (k : ℕ) (as : List ℂ) :
    (X ^ (k + 1) * ofCoeffs (integrateAux k as)).derivative =
      X ^ k * ofCoeffs as := by
  induction as generalizing k with
  | nil => simp [integrateAux, ofCoeffs]
  | cons a as ih =>
    have heq : X ^ (k + 1) * ofCoeffs (integrateAux k (a :: as)) =
        C (a / ((k + 1 : ℕ) : ℂ)) * X ^ (k + 1) +
          X ^ ((k + 1) + 1) * ofCoeffs (integrateAux (k + 1) as) := by
      simp only [integrateAux, ofCoeffs, pow_succ]
      ring
    rw [heq, derivative_add, derivative_C_mul_X_pow, ih]
    have hc : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      div_mul_cancel₀ _ hc, ofCoeffs, pow_succ]
    ring

 theorem ofCoeffs_integrateAux (as : List ℂ) :
    ofCoeffs (0 :: integrateAux 0 as) = antiderivative (ofCoeffs as) := by
  have hd : (ofCoeffs (0 :: integrateAux 0 as)).derivative = ofCoeffs as := by
    simpa [ofCoeffs] using derivative_shifted_integrateAux 0 as
  have hdiff :
      (ofCoeffs (0 :: integrateAux 0 as) - antiderivative (ofCoeffs as)).derivative = 0 := by
    rw [derivative_sub, hd, derivative_antiderivative, sub_self]
  have heq := eq_C_of_derivative_eq_zero hdiff
  have hzero :
      (ofCoeffs (0 :: integrateAux 0 as) - antiderivative (ofCoeffs as)).coeff 0 = 0 := by
    simp [ofCoeffs, coeff_antiderivative_zero]
  rw [hzero, map_zero] at heq
  exact sub_eq_zero.mp heq

 theorem eval_integrateAux (as : List ℂ) (z : ℂ) :
    evalCoeffs (0 :: integrateAux 0 as) z = (antiderivative (ofCoeffs as)).eval z := by
  rw [← eval_ofCoeffs, ofCoeffs_integrateAux]

 theorem eval_productCoeffs (cs : List ℂ) (z : ℂ) :
    evalCoeffs (productCoeffs cs) z = (criticalProduct cs).eval z := by
  rw [← eval_ofCoeffs, ofCoeffs_productCoeffs]

/-- Bridge from ascending-coefficient arithmetic to the all-critical-point property. -/
 theorem criticalBound_of_productCoeffs_normSq (cs : List ℂ)
    (hcs : ∀ c ∈ cs, c ≠ 0) (t : ℝ) (ht : 0 ≤ t)
    (hvalues : ∀ c ∈ cs,
      t ^ 2 * Complex.normSq (evalCoeffs (productCoeffs cs) 0 * c) <
        Complex.normSq (evalCoeffs (0 :: integrateAux 0 (productCoeffs cs)) c)) :
    CriticalBound (prescribedPolynomial cs) t := by
  apply criticalBound_prescribedPolynomial_of_normSq cs hcs t ht
  intro c hc
  simpa only [eval_productCoeffs, eval_integrateAux, ofCoeffs_productCoeffs]
    using hvalues c hc

/-- Strict value inequalities themselves rule out a zero center. -/
 theorem centers_ne_zero_of_productCoeffs_normSq (cs : List ℂ) (t : ℝ)
    (hvalues : ∀ c ∈ cs,
      t ^ 2 * Complex.normSq (evalCoeffs (productCoeffs cs) 0 * c) <
        Complex.normSq (evalCoeffs (0 :: integrateAux 0 (productCoeffs cs)) c)) :
    ∀ c ∈ cs, c ≠ 0 := by
  intro c hc hz
  subst c
  have h := hvalues 0 hc
  simp [eval_integrateAux] at h

/-- A complete algebraic witness package from all coefficient-list value bounds. -/
 theorem prescribedPolynomial_spec_of_productCoeffs_normSq (cs : List ℂ)
    (t : ℝ) (ht : 0 ≤ t)
    (hvalues : ∀ c ∈ cs,
      t ^ 2 * Complex.normSq (evalCoeffs (productCoeffs cs) 0 * c) <
        Complex.normSq (evalCoeffs (0 :: integrateAux 0 (productCoeffs cs)) c)) :
    (prescribedPolynomial cs).natDegree = cs.length + 1 ∧
      (prescribedPolynomial cs).eval 0 = 0 ∧
      (prescribedPolynomial cs).derivative.eval 0 = 1 ∧
      CriticalBound (prescribedPolynomial cs) t := by
  have hcs := centers_ne_zero_of_productCoeffs_normSq cs t hvalues
  exact ⟨natDegree_prescribedPolynomial cs hcs, prescribedPolynomial_eval_zero cs,
    prescribedPolynomial_derivative_eval_zero cs hcs,
    criticalBound_of_productCoeffs_normSq cs hcs t ht hvalues⟩

end Mvc
