import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Error-bounded termination: given the explicit reachability bound
`|err| ≤ 2T·r_max·(V-1)/V` (Theorem~\ref{thm:reach-error}, explicit form, as used in
`app:proof-termination`), and the variation-ratio constraint `V ≤ 2T·r_max/(2T·r_max - ε)`,
the abstraction satisfies `|err| ≤ ε`. The explicit bound enters as a hypothesis here because
its derivation requires the structural assumptions of the appendix; see
`CorAppReach.lean` (`reachability_error_bound_explicit_variation_ratio`) for the chained CTMC
form. -/
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
