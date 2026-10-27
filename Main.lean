import Mvc.Computation
import Mvc.Data.Degree2650
import Mvc.Data.Degree2725
import Mvc.Data.Degree2798
import Mvc.Data.Degree2840
import Mvc.Data.Degree2917

/-- Optional diagnostic executable. The actual proof build independently
proves acceptance and applies the soundness theorem in Mvc.Checker. -/
def main (args : List String) : IO UInt32 := do
  let degree := (args[0]?.getD "2650").toNat!
  let bits := (args[1]?.getD "16000").toNat!
  let (cs,num,den) := match degree with
    | 2650 => (Mvc.Data.degree2650,99964059,100000000)
    | 2725 => (Mvc.Data.degree2725,9996431,10000000)
    | 2798 => (Mvc.Data.degree2798,999649,1000000)
    | 2840 => (Mvc.Data.degree2840,249917,250000)
    | 2917 => (Mvc.Data.degree2917,1000000129,1000000000)
    | _ => ([],0,0)
  IO.println s!"Checking exact degree {degree}, {cs.length} centers, {bits} bits in Lean"
  let result := Mvc.Computation.check bits cs num den
  IO.println s!"check = {result}"
  return if result then 0 else 1
