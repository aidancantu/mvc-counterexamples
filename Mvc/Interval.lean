import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Integer-endpoint intervals at a shared positive natural scale.
All arithmetic soundness proofs are kernel checked; no numerical oracle is used.
-/
namespace Mvc

structure Interval where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

namespace Interval

def Contains (s : Nat) (a : Interval) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ (s : ℝ) * x ∧ (s : ℝ) * x ≤ (a.hi : ℝ)

def zero : Interval := ⟨0, 0⟩
def ofInt (s : Nat) (n : Int) : Interval := ⟨(s : Int) * n, (s : Int) * n⟩
def add (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : Interval) : Interval := ⟨-a.hi, -a.lo⟩
def sub (a b : Interval) : Interval := add a (neg b)

def ceilDiv (a d : Int) : Int := -((-a) / d)

def prodLo (a b : Interval) : Int :=
  min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))
def prodHi (a b : Interval) : Int :=
  max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))

def mul (s : Nat) (a b : Interval) : Interval :=
  ⟨prodLo a b / (s : Int), ceilDiv (prodHi a b) (s : Int)⟩
def divNat (a : Interval) (n : Nat) : Interval :=
  ⟨a.lo / (n : Int), ceilDiv a.hi (n : Int)⟩

theorem contains_zero (s : Nat) : Contains s zero 0 := by
  simp [Contains, zero]

theorem contains_ofInt (s : Nat) (n : Int) : Contains s (ofInt s n) (n : ℝ) := by
  simp [Contains, ofInt]

theorem contains_add {s : Nat} {a b : Interval} {x y : ℝ}
    (hx : Contains s a x) (hy : Contains s b y) : Contains s (add a b) (x + y) := by
  rcases hx with ⟨hxl, hxu⟩
  rcases hy with ⟨hyl, hyu⟩
  constructor <;> simp only [add, Int.cast_add] <;> nlinarith

theorem contains_neg {s : Nat} {a : Interval} {x : ℝ}
    (hx : Contains s a x) : Contains s (neg a) (-x) := by
  rcases hx with ⟨hl, hu⟩
  constructor <;> simp only [neg, Int.cast_neg] <;> nlinarith

theorem contains_sub {s : Nat} {a b : Interval} {x y : ℝ}
    (hx : Contains s a x) (hy : Contains s b y) : Contains s (sub a b) (x - y) := by
  simpa [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

/-- Integer floor division rounds down, also for a negative numerator. -/
theorem floorDiv_mul_le (a : Int) {d : Nat} (hd : 0 < d) :
    ((a / (d : Int) : Int) : ℝ) * (d : ℝ) ≤ (a : ℝ) := by
  have hd' : (d : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  exact_mod_cast (Int.ediv_mul_le a hd')

/-- Negated floor division rounds up, including for a negative numerator. -/
theorem le_ceilDiv_mul (a : Int) {d : Nat} (hd : 0 < d) :
    (a : ℝ) ≤ (ceilDiv a (d : Int) : ℝ) * (d : ℝ) := by
  have h := floorDiv_mul_le (-a) hd
  simp only [ceilDiv, Int.cast_neg] at *
  nlinarith

private theorem lower_mul {l a b x y : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (h1 : l ≤ a * y) (h2 : l ≤ b * y) : l ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact le_trans h1 (mul_le_mul_of_nonneg_right ha hy)
  · exact le_trans h2 (mul_le_mul_of_nonpos_right hb hy)

private theorem upper_mul {u a b x y : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (h1 : a * y ≤ u) (h2 : b * y ≤ u) : x * y ≤ u := by
  rcases le_total 0 y with hy | hy
  · exact le_trans (mul_le_mul_of_nonneg_right hb hy) h2
  · exact le_trans (mul_le_mul_of_nonpos_right ha hy) h1

private theorem four_corner_lower {l a b c d x y : ℝ}
    (hxa : a ≤ x) (hxb : x ≤ b) (hyc : c ≤ y) (hyd : y ≤ d)
    (hac : l ≤ a*c) (had : l ≤ a*d) (hbc : l ≤ b*c) (hbd : l ≤ b*d) :
    l ≤ x*y := by
  have ha : l ≤ y*a := lower_mul hyc hyd (by simpa [mul_comm] using hac)
    (by simpa [mul_comm] using had)
  have hb : l ≤ y*b := lower_mul hyc hyd (by simpa [mul_comm] using hbc)
    (by simpa [mul_comm] using hbd)
  exact lower_mul hxa hxb (by simpa [mul_comm] using ha) (by simpa [mul_comm] using hb)

private theorem four_corner_upper {u a b c d x y : ℝ}
    (hxa : a ≤ x) (hxb : x ≤ b) (hyc : c ≤ y) (hyd : y ≤ d)
    (hac : a*c ≤ u) (had : a*d ≤ u) (hbc : b*c ≤ u) (hbd : b*d ≤ u) :
    x*y ≤ u := by
  have ha : y*a ≤ u := upper_mul hyc hyd (by simpa [mul_comm] using hac)
    (by simpa [mul_comm] using had)
  have hb : y*b ≤ u := upper_mul hyc hyd (by simpa [mul_comm] using hbc)
    (by simpa [mul_comm] using hbd)
  exact upper_mul hxa hxb (by simpa [mul_comm] using ha) (by simpa [mul_comm] using hb)

theorem product_bounds {s : Nat} {a b : Interval} {x y : ℝ}
    (hx : Contains s a x) (hy : Contains s b y) :
    (prodLo a b : ℝ) ≤ ((s : ℝ)*x)*((s : ℝ)*y) ∧
    ((s : ℝ)*x)*((s : ℝ)*y) ≤ (prodHi a b : ℝ) := by
  rcases hx with ⟨hxl, hxu⟩
  rcases hy with ⟨hyl, hyu⟩
  have hl1 : prodLo a b ≤ a.lo*b.lo := min_le_left _ _ |>.trans (min_le_left _ _)
  have hl2 : prodLo a b ≤ a.lo*b.hi := min_le_left _ _ |>.trans (min_le_right _ _)
  have hl3 : prodLo a b ≤ a.hi*b.lo := min_le_right _ _ |>.trans (min_le_left _ _)
  have hl4 : prodLo a b ≤ a.hi*b.hi := min_le_right _ _ |>.trans (min_le_right _ _)
  have hu1 : a.lo*b.lo ≤ prodHi a b := (le_max_left _ _).trans (le_max_left _ _)
  have hu2 : a.lo*b.hi ≤ prodHi a b := (le_max_right _ _).trans (le_max_left _ _)
  have hu3 : a.hi*b.lo ≤ prodHi a b := (le_max_left _ _).trans (le_max_right _ _)
  have hu4 : a.hi*b.hi ≤ prodHi a b := (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · apply four_corner_lower hxl hxu hyl hyu
    · exact_mod_cast hl1
    · exact_mod_cast hl2
    · exact_mod_cast hl3
    · exact_mod_cast hl4
  · apply four_corner_upper hxl hxu hyl hyu
    · exact_mod_cast hu1
    · exact_mod_cast hu2
    · exact_mod_cast hu3
    · exact_mod_cast hu4

theorem contains_mul {s : Nat} (hs : 0 < s) {a b : Interval} {x y : ℝ}
    (hx : Contains s a x) (hy : Contains s b y) : Contains s (mul s a b) (x*y) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨hl, hu⟩ := product_bounds hx hy
  have hfl := floorDiv_mul_le (prodLo a b) hs
  have hcu := le_ceilDiv_mul (prodHi a b) hs
  constructor
  · change ((prodLo a b / (s : Int) : Int) : ℝ) ≤ (s : ℝ) * (x*y)
    apply (mul_le_mul_iff_right₀ hs').mp
    nlinarith
  · change (s : ℝ) * (x*y) ≤ (ceilDiv (prodHi a b) (s : Int) : ℝ)
    apply (mul_le_mul_iff_right₀ hs').mp
    nlinarith

theorem contains_divNat {s n : Nat} (hn : 0 < n) {a : Interval} {x : ℝ}
    (hx : Contains s a x) : Contains s (divNat a n) (x/(n : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfl := floorDiv_mul_le a.lo hn
  have hcu := le_ceilDiv_mul a.hi hn
  rcases hx with ⟨hl, hu⟩
  constructor
  · change ((a.lo / (n : Int) : Int) : ℝ) ≤ (s : ℝ) * (x/(n : ℝ))
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hn').mpr
    exact hfl.trans hl
  · change (s : ℝ) * (x/(n : ℝ)) ≤ (ceilDiv a.hi (n : Int) : ℝ)
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hn').mpr
    exact hu.trans hcu

/-- Enclose an exact rational with positive natural denominator. -/
def ofFrac (s : Nat) (n : Int) (d : Nat) : Interval :=
  ⟨((s : Int)*n) / (d : Int), ceilDiv ((s : Int)*n) (d : Int)⟩

theorem contains_ofFrac (s : Nat) (n : Int) {d : Nat} (hd : 0 < d) :
    Contains s (ofFrac s n d) ((n : ℝ)/(d : ℝ)) := by
  simpa [ofFrac, divNat, ofInt] using contains_divNat hd (contains_ofInt s n)

/-- Multiplication by an exact integer needs no rescaling or rounding. -/
def mulInt (a : Interval) (n : Int) : Interval :=
  ⟨min (a.lo*n) (a.hi*n), max (a.lo*n) (a.hi*n)⟩

theorem contains_mulInt {s : Nat} {a : Interval} {x : ℝ}
    (hx : Contains s a x) (n : Int) : Contains s (mulInt a n) (x*(n : ℝ)) := by
  rcases hx with ⟨hl, hu⟩
  have hll : ((min (a.lo*n) (a.hi*n) : Int) : ℝ) ≤ (a.lo : ℝ)*(n : ℝ) := by
    exact_mod_cast (min_le_left (a.lo*n) (a.hi*n))
  have hlh : ((min (a.lo*n) (a.hi*n) : Int) : ℝ) ≤ (a.hi : ℝ)*(n : ℝ) := by
    exact_mod_cast (min_le_right (a.lo*n) (a.hi*n))
  have hhl : (a.lo : ℝ)*(n : ℝ) ≤ ((max (a.lo*n) (a.hi*n) : Int) : ℝ) := by
    exact_mod_cast (le_max_left (a.lo*n) (a.hi*n))
  have hhh : (a.hi : ℝ)*(n : ℝ) ≤ ((max (a.lo*n) (a.hi*n) : Int) : ℝ) := by
    exact_mod_cast (le_max_right (a.lo*n) (a.hi*n))
  constructor
  · simpa only [mulInt, mul_assoc] using lower_mul hl hu hll hlh
  · simpa only [mulInt, mul_assoc] using upper_mul hl hu hhl hhh

/-- Multiply by an exact rational using small-integer products and one division. -/
def mulFrac (a : Interval) (n : Int) (d : Nat) : Interval := divNat (mulInt a n) d

theorem contains_mulFrac {s : Nat} {a : Interval} {x : ℝ}
    (hx : Contains s a x) (n : Int) {d : Nat} (hd : 0 < d) :
    Contains s (mulFrac a n d) (x*((n : ℝ)/(d : ℝ))) := by
  simpa only [mulFrac, mul_div_assoc] using contains_divNat hd (contains_mulInt hx n)

end Interval
end Mvc
