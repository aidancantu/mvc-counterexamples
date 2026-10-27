import Mvc.RationalComplex

/-! Pure Lean computation on integer enclosures. Its mathematical soundness
is proved in `Mvc.Checker`; executing these functions alone is not a proof. -/
namespace Mvc.Computation

def mulLinearAux (c : RationalComplex) : ComplexBox → List ComplexBox → List ComplexBox
  | prev, [] => [prev]
  | prev, a :: as => (prev.sub (a.mulExact c)) :: mulLinearAux c a as

def productBoxes (s : Nat) : List RationalComplex → List ComplexBox
  | [] => [ComplexBox.one s]
  | c :: cs => mulLinearAux c ComplexBox.zero (productBoxes s cs)

def integrateAux : Nat → List ComplexBox → List ComplexBox
  | _, [] => []
  | k, a :: as => (a.divNat (k+1)) :: integrateAux (k+1) as

def evalBoxes : List ComplexBox → RationalComplex → ComplexBox
  | [], _ => ComplexBox.zero
  | a :: as, c => a.add ((evalBoxes as c).mulExact c)

def zeroPoint : RationalComplex := ⟨0,0,1⟩

def checkAt (s : Nat) (cs : List RationalComplex) (num den : Nat) : Bool :=
  let qs := productBoxes s cs
  let ps := ComplexBox.zero :: integrateAux 0 qs
  let q0 := evalBoxes qs zeroPoint
  decide (0 < s ∧ 0 < den) && cs.all RationalComplex.valid &&
    cs.all (fun c => ComplexBox.ratioCheck (evalBoxes ps c) (q0.mulExact c) num den)

def check (bits : Nat) (cs : List RationalComplex) (num den : Nat) : Bool :=
  checkAt (2^bits) cs num den

end Mvc.Computation
