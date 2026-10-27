import Mvc.Extension

/-!
# Exact degree-range coverage from five strict witnesses

This module proves the covering implication. The five witness hypotheses are
explicit inputs; no numerical certificate is assumed as an axiom here.
-/

namespace Mvc

/-- An exact-degree normalized polynomial whose every critical quotient exceeds
`L`. The definition includes the whole critical set, with no root-count shortcut. -/
def HasWitness (N : ℕ) (L : ℝ) : Prop :=
  ∃ P : Polynomial ℂ, P.natDegree = N ∧ P.eval 0 = 0 ∧
    P.derivative.eval 0 = 1 ∧
    ∀ c : ℂ, P.derivative.eval c = 0 → L < ‖P.eval c / c‖

/-- A strict witness remains a witness at every weaker threshold. -/
theorem HasWitness.mono_bound {N : ℕ} {L T : ℝ} (h : HasWitness N L)
    (hTL : T ≤ L) : HasWitness N T := by
  obtain ⟨P, hdeg, h0, h1, hc⟩ := h
  exact ⟨P, hdeg, h0, h1, fun c hz => lt_of_le_of_lt hTL (hc c hz)⟩

/-- Strict witnesses propagate to every greater exact degree. -/
theorem HasWitness.monotone_degree {n N : ℕ} {L : ℝ} (h : HasWitness n L)
    (hn : 2 ≤ n) (hL : 0 ≤ L) (hnN : n ≤ N) : HasWitness N L := by
  obtain ⟨P, hdeg, h0, h1, hc⟩ := h
  exact exists_degree_extension P h0 h1 (by simpa [hdeg] using hn) hL hc
    (by simpa [hdeg] using hnN)

/-- A convenient exact-arithmetic comparison for the degree-dependent bound. -/
lemma degree_bound_lt_of_product_lt {N : ℕ} (hN : 0 < N) {L : ℝ}
    (h : (N : ℝ) * (1 - L) < 1) : ((N : ℝ) - 1) / (N : ℝ) < L := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  apply (div_lt_iff₀ hNreal).mpr
  nlinarith

lemma degree_bound_lt_one {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) - 1) / (N : ℝ) < 1 := by
  apply degree_bound_lt_of_product_lt hN
  norm_num

/-- The degree-2650 target beats the degree bound throughout its exact range. -/
lemma target2650_covers {N : ℕ} (hN0 : 0 < N) (hN : N ≤ 2782) :
    ((N : ℝ) - 1) / (N : ℝ) < (99964059 : ℝ) / 100000000 := by
  apply degree_bound_lt_of_product_lt hN0
  have hNr : (N : ℝ) ≤ 2782 := by exact_mod_cast hN
  nlinarith

lemma target2725_covers {N : ℕ} (hN0 : 0 < N) (hN : N ≤ 2801) :
    ((N : ℝ) - 1) / (N : ℝ) < (9996431 : ℝ) / 10000000 := by
  apply degree_bound_lt_of_product_lt hN0
  have hNr : (N : ℝ) ≤ 2801 := by exact_mod_cast hN
  nlinarith

lemma target2798_covers {N : ℕ} (hN0 : 0 < N) (hN : N ≤ 2849) :
    ((N : ℝ) - 1) / (N : ℝ) < (999649 : ℝ) / 1000000 := by
  apply degree_bound_lt_of_product_lt hN0
  have hNr : (N : ℝ) ≤ 2849 := by exact_mod_cast hN
  nlinarith

lemma target2840_covers {N : ℕ} (hN0 : 0 < N) (hN : N ≤ 3012) :
    ((N : ℝ) - 1) / (N : ℝ) < (249917 : ℝ) / 250000 := by
  apply degree_bound_lt_of_product_lt hN0
  have hNr : (N : ℝ) ≤ 3012 := by exact_mod_cast hN
  nlinarith

/-- The constant-one counterexample propagates to every degree at least 2917.
The exact degree-2917 witness is a hypothesis, not an unverified certificate. -/
theorem ordinary_all_ge_2917
    (h2917 : HasWitness 2917 ((1000000129 : ℝ) / 1000000000))
    {N : ℕ} (hN : 2917 ≤ N) : HasWitness N 1 := by
  have h := h2917.monotone_degree (by norm_num) (by norm_num) hN
  exact h.mono_bound (by norm_num)

/-- Five exact starting witnesses suffice for a degree-bound counterexample in
EVERY degree at least 2650. All five inputs remain explicit hypotheses. -/
theorem degree_bound_all_ge_2650
    (h2650 : HasWitness 2650 ((99964059 : ℝ) / 100000000))
    (h2725 : HasWitness 2725 ((9996431 : ℝ) / 10000000))
    (h2798 : HasWitness 2798 ((999649 : ℝ) / 1000000))
    (h2840 : HasWitness 2840 ((249917 : ℝ) / 250000))
    (h2917 : HasWitness 2917 ((1000000129 : ℝ) / 1000000000))
    {N : ℕ} (hN : 2650 ≤ N) : HasWitness N (((N : ℝ) - 1) / (N : ℝ)) := by
  have hN0 : 0 < N := by omega
  by_cases hfirst : N ≤ 2782
  · exact (h2650.monotone_degree (by norm_num) (by norm_num) hN).mono_bound
      (target2650_covers hN0 hfirst).le
  by_cases hsecond : N ≤ 2801
  · exact (h2725.monotone_degree (by norm_num) (by norm_num) (by omega)).mono_bound
      (target2725_covers hN0 hsecond).le
  by_cases hthird : N ≤ 2849
  · exact (h2798.monotone_degree (by norm_num) (by norm_num) (by omega)).mono_bound
      (target2798_covers hN0 hthird).le
  by_cases hfourth : N ≤ 3012
  · exact (h2840.monotone_degree (by norm_num) (by norm_num) (by omega)).mono_bound
      (target2840_covers hN0 hfourth).le
  exact (ordinary_all_ge_2917 h2917 (by omega)).mono_bound (degree_bound_lt_one hN0).le

end Mvc
