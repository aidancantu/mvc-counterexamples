import Lean
import Mvc.Data.Degree2650
import Mvc.Data.Degree2725
import Mvc.Data.Degree2798
import Mvc.Data.Degree2840
import Mvc.Data.Degree2917

/- Executable transcription audit, not a theorem or an arithmetic oracle.
Exact cross multiplication compares imported Lean literals with source JSON;
list order and all positive denominators are checked without floating point. -/
open Lean Mvc

private def checked {α : Type} : Except String α → IO α
  | .ok x => pure x
  | .error message => throw (IO.userError message)

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def audit (degree : Nat) (cs : List RationalComplex) : IO Json := do
  let filename := s!"witnesses/{degree}/critical_centers.json"
  let text ← IO.FS.readFile filename
  let document ← checked (Json.parse text)
  let rows ← checked (document.getObjValAs? (Array (Array (Array Int))) "centers")
  require (cs.length + 1 == degree) s!"Lean degree/count mismatch: {degree}"
  require (rows.size == cs.length) s!"JSON/Lean count mismatch: {degree}"
  let mut index := 0
  for c in cs do
    let row := rows[index]!
    require (row.size == 2) s!"Malformed center at {degree}:{index}"
    let rp := row[0]!
    let ip := row[1]!
    require (rp.size == 2 && ip.size == 2) s!"Malformed rational at {degree}:{index}"
    let rn := rp[0]!
    let rd := rp[1]!
    let imn := ip[0]!
    let imd := ip[1]!
    require (decide (0 < rd ∧ 0 < imd ∧ 0 < c.den))
      s!"Nonpositive denominator at {degree}:{index}"
    require (c.re * rd == rn * (c.den : Int)) s!"Real mismatch at {degree}:{index}"
    require (c.im * imd == imn * (c.den : Int)) s!"Imaginary mismatch at {degree}:{index}"
    require c.valid s!"Invalid Lean center at {degree}:{index}"
    index := index + 1
  IO.println s!"PASS degree {degree}: all {index} centers match exactly in order"
  return Json.mkObj [("degree", toJson degree), ("center_count", toJson index),
    ("source_json", toJson filename), ("all_coordinates_exactly_equal_in_order", toJson true),
    ("all_denominators_positive_and_centers_nonzero", toJson true)]

def main : IO Unit := do
  let cases : List (Nat × List RationalComplex) := [
    (2650, Mvc.Data.degree2650), (2725, Mvc.Data.degree2725),
    (2798, Mvc.Data.degree2798), (2840, Mvc.Data.degree2840), (2917, Mvc.Data.degree2917)]
  let results ← cases.mapM fun (degree, cs) => audit degree cs
  let report := Json.mkObj [("status", toJson "passed"),
    ("scope", toJson "Lean executable transcription audit only; not a kernel proof of JSON parsing or numerical certificate acceptance"),
    ("arithmetic", toJson "exact integer cross multiplication; no floating-point coordinates"),
    ("rows", toJson results)]
  IO.FS.writeFile "verification/data_transcription_audit.json" report.pretty
