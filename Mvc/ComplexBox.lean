import Mvc.Interval
import Mathlib.Analysis.Complex.Norm

namespace Mvc

/-- Rectangular complex enclosure; all endpoints are integers at a shared scale. -/
structure ComplexBox where
  re : Interval
  im : Interval
  deriving DecidableEq, Repr

namespace ComplexBox

def Contains (s : Nat) (a : ComplexBox) (z : ℂ) : Prop :=
  a.re.Contains s z.re ∧ a.im.Contains s z.im

def zero : ComplexBox := ⟨Interval.zero, Interval.zero⟩
def one (s : Nat) : ComplexBox := ⟨Interval.ofInt s 1, Interval.zero⟩
def add (a b : ComplexBox) : ComplexBox := ⟨a.re.add b.re, a.im.add b.im⟩
def neg (a : ComplexBox) : ComplexBox := ⟨a.re.neg, a.im.neg⟩
def sub (a b : ComplexBox) : ComplexBox := ⟨a.re.sub b.re, a.im.sub b.im⟩
def mul (s : Nat) (a b : ComplexBox) : ComplexBox :=
  ⟨(Interval.mul s a.re b.re).sub (Interval.mul s a.im b.im),
   (Interval.mul s a.re b.im).add (Interval.mul s a.im b.re)⟩
def divNat (a : ComplexBox) (n : Nat) : ComplexBox := ⟨a.re.divNat n, a.im.divNat n⟩
def ofFrac (s : Nat) (x y : Int) (d : Nat) : ComplexBox :=
  ⟨Interval.ofFrac s x d, Interval.ofFrac s y d⟩

theorem contains_zero (s : Nat) : Contains s zero 0 := by
  exact ⟨Interval.contains_zero s, Interval.contains_zero s⟩

theorem contains_one (s : Nat) : Contains s (one s) 1 := by
  constructor
  · simpa [one] using Interval.contains_ofInt s 1
  · exact Interval.contains_zero s

theorem contains_add {s : Nat} {a b : ComplexBox} {x y : ℂ}
    (hx : Contains s a x) (hy : Contains s b y) : Contains s (add a b) (x+y) := by
  exact ⟨Interval.contains_add hx.1 hy.1, Interval.contains_add hx.2 hy.2⟩

theorem contains_neg {s : Nat} {a : ComplexBox} {x : ℂ}
    (hx : Contains s a x) : Contains s (neg a) (-x) := by
  exact ⟨Interval.contains_neg hx.1, Interval.contains_neg hx.2⟩

theorem contains_sub {s : Nat} {a b : ComplexBox} {x y : ℂ}
    (hx : Contains s a x) (hy : Contains s b y) : Contains s (sub a b) (x-y) := by
  exact ⟨Interval.contains_sub hx.1 hy.1, Interval.contains_sub hx.2 hy.2⟩

theorem contains_mul {s : Nat} (hs : 0 < s) {a b : ComplexBox} {x y : ℂ}
    (hx : Contains s a x) (hy : Contains s b y) : Contains s (mul s a b) (x*y) := by
  exact ⟨Interval.contains_sub (Interval.contains_mul hs hx.1 hy.1)
       (Interval.contains_mul hs hx.2 hy.2),
    Interval.contains_add (Interval.contains_mul hs hx.1 hy.2)
       (Interval.contains_mul hs hx.2 hy.1)⟩

theorem contains_divNat {s n : Nat} (hn : 0 < n) {a : ComplexBox} {x : ℂ}
    (hx : Contains s a x) : Contains s (divNat a n) (x / (n:ℂ)) := by
  constructor
  · simpa [divNat, Complex.div_natCast_re] using Interval.contains_divNat hn hx.1
  · simpa [divNat, Complex.div_natCast_im] using Interval.contains_divNat hn hx.2

theorem contains_ofFrac (s : Nat) (x y : Int) {d : Nat} (hd : 0 < d) :
    Contains s (ofFrac s x y d) (⟨(x:ℝ)/(d:ℝ), (y:ℝ)/(d:ℝ)⟩ : ℂ) := by
  exact ⟨Interval.contains_ofFrac s x hd, Interval.contains_ofFrac s y hd⟩

end ComplexBox

namespace Interval

def sqLo (a : Interval) : Int :=
  if 0 ≤ a.lo then a.lo^2 else if a.hi ≤ 0 then a.hi^2 else 0

def sqHi (a : Interval) : Int := max (a.lo^2) (a.hi^2)

theorem sqLo_le {s : Nat} {a : Interval} {x : ℝ} (h : Contains s a x) :
    (sqLo a : ℝ) ≤ ((s:ℝ)*x)^2 := by
  rcases h with ⟨hl,hu⟩
  unfold sqLo
  split_ifs with hpos hneg
  · have hp : (0:ℝ) ≤ a.lo := by exact_mod_cast hpos
    push_cast
    nlinarith
  · have hn : (a.hi:ℝ) ≤ 0 := by exact_mod_cast hneg
    push_cast
    nlinarith
  · simp only [Int.cast_zero]
    positivity

theorem le_sqHi {s : Nat} {a : Interval} {x : ℝ} (h : Contains s a x) :
    ((s:ℝ)*x)^2 ≤ (sqHi a : ℝ) := by
  rcases h with ⟨hl,hu⟩
  have h1 : (a.lo:ℝ)^2 ≤ (sqHi a:ℝ) := by
    exact_mod_cast (show a.lo^(2:Nat) ≤ sqHi a from le_max_left _ _)
  have h2 : (a.hi:ℝ)^2 ≤ (sqHi a:ℝ) := by
    exact_mod_cast (show a.hi^(2:Nat) ≤ sqHi a from le_max_right _ _)
  rcases le_total 0 ((s:ℝ)*x) with hp | hn
  · nlinarith
  · nlinarith

end Interval

namespace ComplexBox

def normSqLo (a : ComplexBox) : Int := a.re.sqLo + a.im.sqLo
def normSqHi (a : ComplexBox) : Int := a.re.sqHi + a.im.sqHi

theorem normSqLo_le {s : Nat} {a : ComplexBox} {z : ℂ} (h : Contains s a z) :
    (normSqLo a:ℝ) ≤ (s:ℝ)^2 * Complex.normSq z := by
  have hr := Interval.sqLo_le h.1
  have hi := Interval.sqLo_le h.2
  simp only [normSqLo, Int.cast_add, Complex.normSq_apply]
  nlinarith

theorem le_normSqHi {s : Nat} {a : ComplexBox} {z : ℂ} (h : Contains s a z) :
    (s:ℝ)^2 * Complex.normSq z ≤ (normSqHi a:ℝ) := by
  have hr := Interval.le_sqHi h.1
  have hi := Interval.le_sqHi h.2
  simp only [normSqHi, Int.cast_add, Complex.normSq_apply]
  nlinarith

/-- A wholly integer check, used only through its soundness theorem below. -/
def ratioCheck (a b : ComplexBox) (num den : Nat) : Bool :=
  decide (b.normSqHi * (num:Int)^2 < a.normSqLo * (den:Int)^2)

theorem ratioCheck_sound {s : Nat} (hs : 0 < s)
    {a b : ComplexBox} {x y : ℂ} (hx : Contains s a x) (hy : Contains s b y)
    {num den : Nat} (hd : 0 < den) (h : ratioCheck a b num den = true) :
    ((num:ℝ)/(den:ℝ))^2 * Complex.normSq y < Complex.normSq x := by
  have hcheck : b.normSqHi * (num:Int)^2 < a.normSqLo * (den:Int)^2 := by
    simpa [ratioCheck] using h
  have hcheckR : (b.normSqHi:ℝ) * (num:ℝ)^2 < (a.normSqLo:ℝ) * (den:ℝ)^2 := by
    exact_mod_cast hcheck
  have hx' := normSqLo_le hx
  have hy' := le_normSqHi hy
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hdR : (0:ℝ) < den := by exact_mod_cast hd
  have hl := mul_le_mul_of_nonneg_right hy' (sq_nonneg (num:ℝ))
  have hu := mul_le_mul_of_nonneg_right hx' (sq_nonneg (den:ℝ))
  have hmul : (s:ℝ)^2 * (Complex.normSq y * (num:ℝ)^2) <
      (s:ℝ)^2 * (Complex.normSq x * (den:ℝ)^2) := by nlinarith
  have hcore := (mul_lt_mul_iff_right₀ (sq_pos_of_pos hsR)).mp hmul
  rw [div_pow, div_mul_eq_mul_div, div_lt_iff₀ (sq_pos_of_pos hdR)]
  nlinarith

end ComplexBox
end Mvc
