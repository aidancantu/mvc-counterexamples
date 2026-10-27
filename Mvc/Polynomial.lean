import Mathlib

/-!
# Exact polynomials with a prescribed critical multiset

The construction uses a monic product and coefficientwise antiderivation.
The list is allowed to contain repeated centers. Concrete arithmetic certificates
are separate from the algebraic and norm-comparison lemmas in this file.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Mvc

/-- Monic product whose full zero multiset is the supplied list. -/
def criticalProduct : List ℂ → ℂ[X]
  | [] => 1
  | c :: cs => (X - C c) * criticalProduct cs

/-- Coefficientwise primitive with zero constant coefficient. -/
def antiderivative (p : ℂ[X]) : ℂ[X] :=
  p.sum fun n a => monomial (n + 1) (a / ((n + 1 : ℕ) : ℂ))

/-- Exact normalized primitive of the monic critical product. -/
def prescribedPolynomial (cs : List ℂ) : ℂ[X] :=
  C ((criticalProduct cs).eval 0)⁻¹ * antiderivative (criticalProduct cs)

/-- A bound at every complex critical point, with no simplicity assumption. -/
def CriticalBound (P : ℂ[X]) (L : ℝ) : Prop :=
  ∀ z : ℂ, P.derivative.eval z = 0 → L < ‖P.eval z / z‖

 theorem criticalProduct_eq_list_prod (cs : List ℂ) :
    criticalProduct cs = (cs.map fun c => X - C c).prod := by
  induction cs with
  | nil => simp [criticalProduct]
  | cons c cs ih => simp [criticalProduct, ih]

 theorem criticalProduct_monic (cs : List ℂ) : (criticalProduct cs).Monic := by
  induction cs with
  | nil => simp [criticalProduct]
  | cons c cs ih => exact (monic_X_sub_C c).mul ih

 theorem criticalProduct_ne_zero (cs : List ℂ) : criticalProduct cs ≠ 0 :=
  (criticalProduct_monic cs).ne_zero

 theorem natDegree_criticalProduct (cs : List ℂ) :
    (criticalProduct cs).natDegree = cs.length := by
  induction cs with
  | nil => simp [criticalProduct]
  | cons c cs ih =>
    rw [criticalProduct, natDegree_mul (X_sub_C_ne_zero c) (criticalProduct_ne_zero cs)]
    simp [ih, Nat.add_comm]

 theorem criticalProduct_eval_eq_zero_iff (cs : List ℂ) (z : ℂ) :
    (criticalProduct cs).eval z = 0 ↔ z ∈ cs := by
  induction cs with
  | nil => simp [criticalProduct]
  | cons c cs ih => simp [criticalProduct, ih, sub_eq_zero]

 theorem criticalProduct_eval_zero_ne_zero (cs : List ℂ)
    (hcs : ∀ c ∈ cs, c ≠ 0) : (criticalProduct cs).eval 0 ≠ 0 := by
  intro h
  exact hcs 0 ((criticalProduct_eval_eq_zero_iff cs 0).mp h) rfl

 theorem derivative_antiderivative (p : ℂ[X]) :
    (antiderivative p).derivative = p := by
  classical
  unfold antiderivative
  rw [Polynomial.sum_def, derivative_sum]
  calc
    (∑ n ∈ p.support,
      (monomial (n + 1) (p.coeff n / ((n + 1 : ℕ) : ℂ))).derivative)
        = ∑ n ∈ p.support, monomial n (p.coeff n) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hc : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp [derivative_monomial_succ, Nat.cast_add, Nat.cast_one, hc]
    _ = p := by simpa [Polynomial.sum_def] using (Polynomial.sum_monomial_eq p)

 @[simp] theorem antiderivative_eval_zero (p : ℂ[X]) :
    (antiderivative p).eval 0 = 0 := by
  classical
  simp [antiderivative, Polynomial.sum_def, eval_finset_sum]

 @[simp] theorem coeff_antiderivative_zero (p : ℂ[X]) :
    (antiderivative p).coeff 0 = 0 := by
  classical
  simp [antiderivative, Polynomial.sum_def, coeff_monomial]

 theorem coeff_antiderivative_succ (p : ℂ[X]) (n : ℕ) :
    (antiderivative p).coeff (n + 1) = p.coeff n / ((n + 1 : ℕ) : ℂ) := by
  have hc : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  apply (eq_div_iff hc).2
  have h := congrArg (fun f : ℂ[X] => f.coeff n) (derivative_antiderivative p)
  simpa only [coeff_derivative, Nat.cast_add, Nat.cast_one] using h

 theorem natDegree_antiderivative (p : ℂ[X]) (hp : p ≠ 0) :
    (antiderivative p).natDegree = p.natDegree + 1 := by
  have hpos : 0 < (antiderivative p).natDegree := by
    by_contra h
    have hz : (antiderivative p).natDegree = 0 := Nat.eq_zero_of_not_pos h
    have hd := derivative_of_natDegree_zero hz
    rw [derivative_antiderivative] at hd
    exact hp hd
  have hdeg := natDegree_eq_of_degree_eq_some
    (degree_derivative_eq (antiderivative p) hpos)
  rw [derivative_antiderivative] at hdeg
  omega

 theorem derivative_prescribedPolynomial (cs : List ℂ) :
    (prescribedPolynomial cs).derivative =
      C ((criticalProduct cs).eval 0)⁻¹ * criticalProduct cs := by
  simp [prescribedPolynomial, derivative_antiderivative]

 @[simp] theorem prescribedPolynomial_eval_zero (cs : List ℂ) :
    (prescribedPolynomial cs).eval 0 = 0 := by
  simp [prescribedPolynomial]

 theorem prescribedPolynomial_derivative_eval_zero (cs : List ℂ)
    (hcs : ∀ c ∈ cs, c ≠ 0) :
    (prescribedPolynomial cs).derivative.eval 0 = 1 := by
  simp [derivative_prescribedPolynomial, criticalProduct_eval_zero_ne_zero cs hcs]

 theorem prescribedPolynomial_critical_iff (cs : List ℂ)
    (hcs : ∀ c ∈ cs, c ≠ 0) (z : ℂ) :
    (prescribedPolynomial cs).derivative.eval z = 0 ↔ z ∈ cs := by
  simp [derivative_prescribedPolynomial,
    criticalProduct_eval_zero_ne_zero cs hcs, criticalProduct_eval_eq_zero_iff]

 theorem natDegree_prescribedPolynomial (cs : List ℂ)
    (hcs : ∀ c ∈ cs, c ≠ 0) :
    (prescribedPolynomial cs).natDegree = cs.length + 1 := by
  rw [prescribedPolynomial,
    natDegree_C_mul (inv_ne_zero (criticalProduct_eval_zero_ne_zero cs hcs)),
    natDegree_antiderivative _ (criticalProduct_ne_zero cs), natDegree_criticalProduct]

 theorem prescribedPolynomial_quotient (cs : List ℂ) (z : ℂ) :
    (prescribedPolynomial cs).eval z / z =
      (antiderivative (criticalProduct cs)).eval z /
        ((criticalProduct cs).eval 0 * z) := by
  simp [prescribedPolynomial, div_eq_mul_inv, mul_comm, mul_left_comm]

 theorem norm_div_gt_of_normSq_gt (a d : ℂ) (t : ℝ)
    (ht : 0 ≤ t) (hd : d ≠ 0)
    (h : t ^ 2 * Complex.normSq d < Complex.normSq a) :
    t < ‖a / d‖ := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  have hmul : t * ‖d‖ < ‖a‖ := by
    apply (sq_lt_sq₀ (mul_nonneg ht (norm_nonneg d)) (norm_nonneg a)).mp
    simpa [mul_pow] using h
  rw [norm_div]
  exact (lt_div_iff₀ (norm_pos_iff.mpr hd)).2 hmul

 theorem criticalBound_prescribedPolynomial_of_normSq (cs : List ℂ)
    (hcs : ∀ c ∈ cs, c ≠ 0) (t : ℝ) (ht : 0 ≤ t)
    (hvalues : ∀ c ∈ cs,
      t ^ 2 * Complex.normSq ((criticalProduct cs).eval 0 * c) <
        Complex.normSq ((antiderivative (criticalProduct cs)).eval c)) :
    CriticalBound (prescribedPolynomial cs) t := by
  intro c hc
  have hmem := (prescribedPolynomial_critical_iff cs hcs c).mp hc
  rw [prescribedPolynomial_quotient]
  exact norm_div_gt_of_normSq_gt _ _ t ht
    (mul_ne_zero (criticalProduct_eval_zero_ne_zero cs hcs) (hcs c hmem))
    (hvalues c hmem)

end Mvc
