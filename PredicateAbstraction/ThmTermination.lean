import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Error-bounded termination inequality from Theorem 6. -/
theorem errorBoundedTermination
    (ε T rmax V err : ℝ)
    (_hε : 0 < ε)
    (hε_lt : ε < 2 * T * rmax)
    (hVpos : 0 < V)
    (herr : |err| ≤ 2 * T * rmax * (V - 1) / V)
    (hV :
      V ≤ (2 * T * rmax) / (2 * T * rmax - ε)) :
    |err| ≤ ε
 :=
  errorBoundedTermination_core ε T rmax V err _hε hε_lt hVpos herr hV

end PredicateAbstraction.PaperProofs
