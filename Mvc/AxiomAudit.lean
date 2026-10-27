import Mvc.Results

-- The generic analytic/arithmetic theorems use only standard mathlib axioms.
#print axioms Mvc.exists_degree_extension
#print axioms Mvc.check_sound_full
-- Concrete computations use native_decide: compiler/runtime trust is explicit.
#print axioms Mvc.Results.explicit_degree_2650
#print axioms Mvc.Results.explicit_degree_2917
#print axioms Mvc.Results.every_degree_ge_2650
#print axioms Mvc.Results.every_degree_ge_2917
