import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Variation–error correspondence: the residence-time error on a region `I` is bounded by
`‖δ‖∞·|I|·V / rmax`, where `V = rmax / rmin`. The bound is derived from the per-interval
error bound `errorBoundNonUniformEntry`, not assumed as a hypothesis. -/
theorem variationErrorCorrespondence
    (I : Finset α) (hI : I.Nonempty) (δ r : α → ℝ) (rmin rmax V : ℝ)
    (hrmin : 0 < rmin) (hrmax : 0 < rmax)
    (hr_lower : ∀ x ∈ I, rmin ≤ r x)
    (hV : V = rmax / rmin) :
    let err : ℝ := ∑ x ∈ I, δ x * (1 / r x)
    |err| ≤ deviationNorm I hI δ * ((I.card : ℝ)) * V / rmax
 :=
  variationErrorCorrespondence_fromErrorBound_core
    I hI δ r rmin rmax V hrmin hrmax hr_lower hV

end PredicateAbstraction.PaperProofs
