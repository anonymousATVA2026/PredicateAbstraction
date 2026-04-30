import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Harmonic-mean aggregation preserves expected residence time. -/
theorem harmonicMeanAggregation
    (I : Finset α) (hI : I.Nonempty) (r : α → ℝ)
    (hr : ∀ x ∈ I, 0 < r x) :
    let avgInv := (1 / (I.card : ℝ)) * (∑ x ∈ I, (1 / r x))
    let rHat : ℝ := avgInv⁻¹
    1 / rHat = avgInv
 :=
  harmonicMeanAggregation_core I hI r hr

end PredicateAbstraction.PaperProofs
