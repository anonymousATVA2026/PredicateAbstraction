import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- The paper's single-interval bound using `deviationNorm = ‖δ‖∞`. -/
theorem errorBoundNonUniformEntry_supNorm
    (I : Finset α) (hI : I.Nonempty) (δ r : α → ℝ) (rmin : ℝ)
    (hrmin : 0 < rmin)
    (hr_lower : ∀ x ∈ I, rmin ≤ r x) :
    let err : ℝ := ∑ x ∈ I, δ x * (1 / r x)
    |err| ≤ deviationNorm I hI δ * (I.card : ℝ) / rmin
 :=
  errorBoundNonUniformEntry_supNorm_core I hI δ r rmin hrmin hr_lower

end PredicateAbstraction.PaperProofs
