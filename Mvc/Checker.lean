import Mvc.Computation
import Mvc.Coefficients

/-!
# Executable interval checker and its mathematical soundness

The checker uses only integer operations on enclosures and exact rational input
coordinates. Its successful evaluation is a separate obligation for each witness.
-/

namespace Mvc

/-- Pointwise semantic enclosure of a coefficient list. -/
def CoeffContains (s : Nat) (bs : List ComplexBox) (as : List ℂ) : Prop :=
  List.Forall₂ (fun b a => b.Contains s a) bs as

theorem mulLinearBoxes_contains {s : Nat} (c : RationalComplex) (hd : 0 < c.den)
    {prev : ComplexBox} {p : ℂ} {bs : List ComplexBox} {as : List ℂ}
    (hp : prev.Contains s p) (h : CoeffContains s bs as) :
    CoeffContains s (Computation.mulLinearAux c prev bs) (mulLinearAux c.value p as) := by
  induction h generalizing prev p with
  | nil => exact List.Forall₂.cons hp List.Forall₂.nil
  | @cons b a bs as hba htail ih =>
    apply List.Forall₂.cons
    · simpa only [Computation.mulLinearAux, mulLinearAux, mul_comm] using
        ComplexBox.contains_sub hp (ComplexBox.contains_mulExact hba c hd)
    · exact ih hba

theorem productBoxes_contains (s : Nat) (cs : List RationalComplex)
    (hvalid : ∀ c ∈ cs, 0 < c.den) :
    CoeffContains s (Computation.productBoxes s cs) (productCoeffs (cs.map RationalComplex.value)) := by
  induction cs with
  | nil => exact List.Forall₂.cons (ComplexBox.contains_one s) List.Forall₂.nil
  | cons c cs ih =>
    apply mulLinearBoxes_contains c (hvalid c (by simp)) (ComplexBox.contains_zero s)
    apply ih
    intro d hd
    exact hvalid d (by simp [hd])

theorem integrateBoxes_contains {s : Nat} (k : Nat) {bs : List ComplexBox} {as : List ℂ}
    (h : CoeffContains s bs as) :
    CoeffContains s (Computation.integrateAux k bs) (integrateAux k as) := by
  induction h generalizing k with
  | nil => exact List.Forall₂.nil
  | @cons b a bs as hba htail ih =>
    exact List.Forall₂.cons (ComplexBox.contains_divNat (Nat.zero_lt_succ k) hba) (ih (k+1))

theorem evalBoxes_contains {s : Nat} {bs : List ComplexBox} {as : List ℂ}
    (h : CoeffContains s bs as) (c : RationalComplex) (hd : 0 < c.den) :
    (Computation.evalBoxes bs c).Contains s (evalCoeffs as c.value) := by
  induction h with
  | nil => exact ComplexBox.contains_zero s
  | @cons b a bs as hba htail ih =>
    simpa only [Computation.evalBoxes, evalCoeffs, mul_comm] using
      ComplexBox.contains_add hba (ComplexBox.contains_mulExact ih c hd)

@[simp] theorem zeroPoint_value : Computation.zeroPoint.value = 0 := by
  apply Complex.ext <;> simp [Computation.zeroPoint, RationalComplex.value]

/-- Successful checking proves the bound at every complex critical point.
The theorem does not postulate acceptance of any concrete numerical data. -/
theorem checkAt_sound {s : Nat} {cs : List RationalComplex} {num den : Nat}
    (h : Computation.checkAt s cs num den = true) :
    CriticalBound (prescribedPolynomial (cs.map RationalComplex.value))
      ((num : ℝ)/(den : ℝ)) := by
  simp only [Computation.checkAt, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hs, hd⟩, hvalid⟩, hchecks⟩ := h
  have hpos : ∀ c ∈ cs, 0 < c.den := fun c hc => RationalComplex.valid_pos (hvalid c hc)
  have hnonzero : ∀ c ∈ cs.map RationalComplex.value, c ≠ 0 := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    exact RationalComplex.valid_ne_zero (hvalid c hc)
  apply criticalBound_prescribedPolynomial_of_normSq _ hnonzero _ (by positivity)
  intro z hz
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
  have hq := productBoxes_contains s cs hpos
  have ha : CoeffContains s (ComplexBox.zero :: Computation.integrateAux 0 (Computation.productBoxes s cs))
      (0 :: integrateAux 0 (productCoeffs (cs.map RationalComplex.value))) :=
    List.Forall₂.cons (ComplexBox.contains_zero s) (integrateBoxes_contains 0 hq)
  have hnum := evalBoxes_contains ha c (hpos c hc)
  have hzero := evalBoxes_contains hq Computation.zeroPoint (by decide)
  have hden := ComplexBox.contains_mulExact hzero c (hpos c hc)
  have result := ComplexBox.ratioCheck_sound hs hnum hden hd (hchecks c hc)
  simpa only [zeroPoint_value, eval_integrateAux, ofCoeffs_productCoeffs,
    eval_productCoeffs] using result

/-- The precision-indexed executable checker inherits the scale checker's soundness. -/
theorem check_sound {bits : Nat} {cs : List RationalComplex} {num den : Nat}
    (h : Computation.check bits cs num den = true) :
    CriticalBound (prescribedPolynomial (cs.map RationalComplex.value))
      ((num : ℝ)/(den : ℝ)) :=
  checkAt_sound h

/-- All normalization and degree facts accompany a successful certificate. -/
theorem check_sound_full {bits : Nat} {cs : List RationalComplex} {num den : Nat}
    (h : Computation.check bits cs num den = true) :
    (prescribedPolynomial (cs.map RationalComplex.value)).natDegree = cs.length + 1 ∧
    (prescribedPolynomial (cs.map RationalComplex.value)).eval 0 = 0 ∧
    (prescribedPolynomial (cs.map RationalComplex.value)).derivative.eval 0 = 1 ∧
    CriticalBound (prescribedPolynomial (cs.map RationalComplex.value))
      ((num : ℝ)/(den : ℝ)) := by
  have hb := h
  simp only [Computation.check, Computation.checkAt, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hb
  have hvalid := hb.1.2
  have hnonzero : ∀ c ∈ cs.map RationalComplex.value, c ≠ 0 := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    exact RationalComplex.valid_ne_zero (hvalid c hc)
  refine ⟨?_, prescribedPolynomial_eval_zero _,
    prescribedPolynomial_derivative_eval_zero _ hnonzero, check_sound h⟩
  simpa using natDegree_prescribedPolynomial (cs.map RationalComplex.value) hnonzero

end Mvc
