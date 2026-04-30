import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Variation-error correspondence from the refinement section. -/
theorem variationErrorCorrespondence
    (err δInf regionSize rmax rmin V : ℝ)
    (hbound : |err| ≤ δInf * regionSize / rmin)
    (hV : V = rmax / rmin)
    (hrmin : 0 < rmin) (hrmax : 0 < rmax) :
    |err| ≤ δInf * regionSize * V / rmax
 :=
  variationErrorCorrespondence_core err δInf regionSize rmax rmin V hbound hV hrmin hrmax

end PredicateAbstraction.PaperProofs
