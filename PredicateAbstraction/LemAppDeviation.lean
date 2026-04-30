import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Interval deviation bound in variation-ratio form. -/
theorem deviationBoundFromVariationRatio
    (x xhat rmin rmax V : ℝ)
    (hx_lower : rmin ≤ x)
    (hx_upper : x ≤ rmax)
    (hxhat_lower : rmin ≤ xhat)
    (hxhat_upper : xhat ≤ rmax)
    (hrmin : 0 < rmin)
    (hV : V = rmax / rmin) :
    |x - xhat| ≤ rmax * (V - 1) / V
 :=
  deviationBoundFromVariationRatio_core x xhat rmin rmax V hx_lower hx_upper hxhat_lower hxhat_upper hrmin hV

end PredicateAbstraction.PaperProofs
