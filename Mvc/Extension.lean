import Mathlib

/-!
# Strict degree extension for normalized complex polynomials

The proof uses a compact sublevel set, not continuity of individual critical
roots. No witness certificate or numerical assumption enters this module.
-/

open Polynomial Set

namespace Mvc

/-- A nonvanishing continuous function on a compact set remains nonvanishing
under every sufficiently small scalar multiple of another continuous function. -/
lemma compact_nonzero_add_small {E : Set ℂ} (hE : IsCompact E)
    {f g : ℂ → ℂ} (hf : ContinuousOn f E) (hg : ContinuousOn g E)
    (hn : ∀ z ∈ E, f z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, ‖ε‖ < δ → ∀ z ∈ E, f z + ε * g z ≠ 0 := by
  obtain ⟨A, hA, hAf⟩ := hE.exists_forall_le' hf.norm
    (fun z hz => norm_pos_iff.mpr (hn z hz))
  obtain ⟨B, hB⟩ := hE.exists_bound_of_continuousOn hg
  let D : ℝ := max B 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨A / D, div_pos hA hD, ?_⟩
  intro ε hε z hz
  have hBD : ‖g z‖ ≤ D := by
    exact (hB z hz).trans (le_trans (le_max_left B 0) (by dsimp [D]; linarith))
  have hsmall : ‖ε * g z‖ < ‖f z‖ := by
    rw [norm_mul]
    calc
      ‖ε‖ * ‖g z‖ ≤ ‖ε‖ * D := mul_le_mul_of_nonneg_left hBD (norm_nonneg _)
      _ < A := (lt_div_iff₀ hD).mp hε
      _ ≤ ‖f z‖ := hAf z hz
  intro heq
  have heq' : f z = -(ε * g z) := eq_neg_of_add_eq_zero_left heq
  rw [heq', norm_neg] at hsmall
  exact (lt_irrefl _) hsmall

/-- The critical quotient of the perturbation will equal this polynomial. -/
noncomputable def extensionQuotient (P : ℂ[X]) (N : ℕ) : ℂ[X] :=
  P.divX - C ((N : ℂ)⁻¹) * P.derivative

lemma divX_eval_eq_div (P : ℂ[X]) (hP : P.eval 0 = 0) {z : ℂ} (hz : z ≠ 0) :
    P.divX.eval z = P.eval z / z := by
  have hcoeff : P.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero]; exact hP
  have h := congrArg (fun R : ℂ[X] => R.eval z) (P.divX_mul_X_add)
  simp only [eval_add, eval_mul, eval_X, eval_C, hcoeff, add_zero] at h
  exact (eq_div_iff hz).mpr h

lemma extensionQuotient_eval (P : ℂ[X]) (N : ℕ) (hP : P.eval 0 = 0)
    {z : ℂ} (hz : z ≠ 0) :
    (extensionQuotient P N).eval z = P.eval z / z - P.derivative.eval z / (N : ℂ) := by
  simp [extensionQuotient, divX_eval_eq_div P hP hz, div_eq_mul_inv, mul_comm]

lemma extensionQuotient_degree_pos (P : ℂ[X]) (hn : 2 ≤ P.natDegree)
    {N : ℕ} (hN : P.natDegree < N) : 0 < (extensionQuotient P N).degree := by
  have hP : P ≠ 0 := by intro heq; simp [heq] at hn
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hn0 : P.natDegree - 1 + 1 = P.natDegree := by omega
  have hcast : ((P.natDegree - 1 : ℕ) : ℂ) + 1 = (P.natDegree : ℂ) := by
    exact_mod_cast hn0
  have hcoeff : (extensionQuotient P N).coeff (P.natDegree - 1) ≠ 0 := by
    rw [extensionQuotient, coeff_sub, coeff_C_mul, coeff_divX, coeff_derivative, hn0]
    simp only [hcast]
    rw [show P.coeff P.natDegree = P.leadingCoeff from rfl]
    have ha := leadingCoeff_ne_zero.mpr hP
    have hne : (N : ℂ) ≠ (P.natDegree : ℂ) := by
      exact_mod_cast (ne_of_gt hN)
    intro heq
    have hmul : P.leadingCoeff * ((N : ℂ) - (P.natDegree : ℂ)) = 0 := by
      field_simp at heq
      linear_combination heq
    rcases mul_eq_zero.mp hmul with h | h
    · exact ha h
    · exact hne (sub_eq_zero.mp h)
  apply natDegree_pos_iff_degree_pos.mp
  exact lt_of_lt_of_le (by omega : 0 < P.natDegree - 1) (le_natDegree_of_ne_zero hcoeff)

/-- Adding a nonzero coefficient in a strictly larger degree has that exact degree. -/
lemma perturb_natDegree (P : ℂ[X]) {N : ℕ} (hN : P.natDegree < N)
    {ε : ℂ} (hε : ε ≠ 0) : (P + C ε * X ^ N).natDegree = N := by
  have h := natDegree_C_mul_X_pow N ε hε
  rw [natDegree_add_eq_right_of_natDegree_lt (by simpa [h] using hN), h]

lemma perturb_derivative_eval (P : ℂ[X]) (N : ℕ) (ε z : ℂ) :
    (P + C ε * X ^ N).derivative.eval z =
      P.derivative.eval z + ε * ((N : ℂ) * z ^ (N - 1)) := by
  simp [derivative_add, derivative_mul, derivative_X_pow]

lemma perturb_eval_zero (P : ℂ[X]) (hP : P.eval 0 = 0) {N : ℕ} (hN : 0 < N)
    (ε : ℂ) : (P + C ε * X ^ N).eval 0 = 0 := by
  simp [hP, ne_of_gt hN]

lemma perturb_derivative_eval_zero (P : ℂ[X]) (hP : P.derivative.eval 0 = 1)
    {N : ℕ} (hN : 2 ≤ N) (ε : ℂ) :
    (P + C ε * X ^ N).derivative.eval 0 = 1 := by
  rw [perturb_derivative_eval, hP]
  simp [show N - 1 ≠ 0 by omega]

lemma perturb_critical_quotient (P : ℂ[X]) (hP : P.eval 0 = 0)
    {N : ℕ} (hN : 0 < N) (ε : ℂ) {z : ℂ} (hz : z ≠ 0)
    (hc : (P + C ε * X ^ N).derivative.eval z = 0) :
    (P + C ε * X ^ N).eval z / z = (extensionQuotient P N).eval z := by
  rw [extensionQuotient_eval P N hP hz]
  rw [perturb_derivative_eval] at hc
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hpow : z ^ N = z ^ (N - 1) * z := by
    conv_lhs => rw [← Nat.sub_add_cancel hN, pow_succ]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  rw [hpow]
  field_simp
  linear_combination z * hc

/-- Every sufficiently small nonzero higher-degree monomial perturbation
preserves a strict lower bound on every critical quotient. -/
theorem degree_extension_small (P : ℂ[X])
    (hP0 : P.eval 0 = 0) (hP1 : P.derivative.eval 0 = 1)
    (hn : 2 ≤ P.natDegree) {L : ℝ} (_hL : 0 ≤ L)
    (hcrit : ∀ c : ℂ, P.derivative.eval c = 0 → L < ‖P.eval c / c‖)
    {N : ℕ} (hN : P.natDegree < N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, ε ≠ 0 → ‖ε‖ < δ →
      (P + C ε * X ^ N).natDegree = N ∧
      (P + C ε * X ^ N).eval 0 = 0 ∧
      (P + C ε * X ^ N).derivative.eval 0 = 1 ∧
      ∀ c : ℂ, (P + C ε * X ^ N).derivative.eval c = 0 →
        L < ‖(P + C ε * X ^ N).eval c / c‖ := by
  let H := extensionQuotient P N
  let E : Set ℂ := H.eval ⁻¹' Metric.closedBall 0 L
  have hH : 0 < H.degree := extensionQuotient_degree_pos P hn hN
  have hE : IsCompact E := (H.isProperMap_eval hH).isCompact_preimage
    (isCompact_closedBall 0 L)
  have hnonzero : ∀ z ∈ E, P.derivative.eval z ≠ 0 := by
    intro z hz hzero
    have hz0 : z ≠ 0 := by
      intro heq
      subst z
      rw [hP1] at hzero
      exact one_ne_zero hzero
    have hval : H.eval z = P.eval z / z := by
      dsimp [H]
      rw [extensionQuotient_eval P N hP0 hz0, hzero]
      simp
    have hle : ‖H.eval z‖ ≤ L := by
      simpa only [E, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hz
    rw [hval] at hle
    exact (not_lt_of_ge hle) (hcrit z hzero)
  obtain ⟨δ, hδ, hδprop⟩ := compact_nonzero_add_small hE
    P.derivative.continuous.continuousOn
    (show ContinuousOn (fun z : ℂ => (N : ℂ) * z ^ (N - 1)) E by fun_prop)
    hnonzero
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hN2 : 2 ≤ N := by omega
  refine ⟨perturb_natDegree P hN hε,
    perturb_eval_zero P hP0 (by omega) ε,
    perturb_derivative_eval_zero P hP1 hN2 ε, ?_⟩
  intro c hc
  have hc0 : c ≠ 0 := by
    intro heq
    subst c
    rw [perturb_derivative_eval_zero P hP1 hN2 ε] at hc
    exact one_ne_zero hc
  have hid := perturb_critical_quotient P hP0 (by omega : 0 < N) ε hc0 hc
  by_contra hbad
  have hce : c ∈ E := by
    have hle := le_of_not_gt hbad
    rw [hid] at hle
    simpa only [E, H, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hle
  exact hδprop ε hεδ c hce (by simpa only [perturb_derivative_eval] using hc)

/-- Strict critical-quotient witnesses extend to every larger exact degree.
All inputs are mathematical hypotheses; no certificate data are assumed. -/
theorem exists_degree_extension (P : ℂ[X])
    (hP0 : P.eval 0 = 0) (hP1 : P.derivative.eval 0 = 1)
    (hn : 2 ≤ P.natDegree) {L : ℝ} (hL : 0 ≤ L)
    (hcrit : ∀ c : ℂ, P.derivative.eval c = 0 → L < ‖P.eval c / c‖)
    {N : ℕ} (hN : P.natDegree ≤ N) :
    ∃ Q : ℂ[X], Q.natDegree = N ∧ Q.eval 0 = 0 ∧ Q.derivative.eval 0 = 1 ∧
      ∀ c : ℂ, Q.derivative.eval c = 0 → L < ‖Q.eval c / c‖ := by
  rcases eq_or_lt_of_le hN with heq | hlt
  · exact ⟨P, heq, hP0, hP1, hcrit⟩
  obtain ⟨δ, hδ, hprop⟩ := degree_extension_small P hP0 hP1 hn hL hcrit hlt
  let ε : ℂ := (δ / 2 : ℝ)
  have hεpos : 0 < δ / 2 := half_pos hδ
  have hε : ε ≠ 0 := by
    dsimp [ε]
    exact_mod_cast (ne_of_gt hεpos)
  have hnorm : ‖ε‖ < δ := by
    dsimp [ε]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpos]
    linarith
  exact ⟨P + C ε * X ^ N, hprop ε hε hnorm⟩

end Mvc
