import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Harmonic-mean aggregation achieves temporal preservation: under uniform entry
on `I`, the expected residence time `∑ x∈I, p(x)·1/r(x)` equals `1/rHat`, where
`rHat = ((1/|I|)·∑ 1/r(x))⁻¹` is the harmonic-mean rate. -/
theorem harmonicMeanAggregation
    (I : Finset α) (hI : I.Nonempty) (r p : α → ℝ)
    (hr : ∀ x ∈ I, 0 < r x)
    (hp : ∀ x ∈ I, p x = 1 / (I.card : ℝ)) :
    let avgInv := (1 / (I.card : ℝ)) * (∑ x ∈ I, (1 / r x))
    let rHat : ℝ := avgInv⁻¹
    (∑ x ∈ I, p x * (1 / r x)) = 1 / rHat
 :=
  harmonicMean_temporalPreservation_core I hI r p hr hp

end PredicateAbstraction.PaperProofs
