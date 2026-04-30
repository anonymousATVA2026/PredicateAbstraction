import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Single-variable total error bound across interval partitions. -/
theorem singleVariableTotalErrorBound
    (J : Finset ι) (I : ι → Finset α) (δ : ι → α → ℝ) (r : α → ℝ)
    (rmin δInf : ι → ℝ)
    (hrmin : ∀ j ∈ J, 0 < rmin j)
    (hδ : ∀ j ∈ J, ∀ x ∈ I j, |δ j x| ≤ δInf j)
    (hr_lower : ∀ j ∈ J, ∀ x ∈ I j, rmin j ≤ r x) :
    let totalErr : ℝ := ∑ j ∈ J, ∑ x ∈ I j, δ j x * (1 / r x)
    |totalErr| ≤ ∑ j ∈ J, δInf j * ((I j).card : ℝ) / rmin j
 :=
  singleVariableTotalErrorBound_core J I δ r rmin δInf hrmin hδ hr_lower

end PredicateAbstraction.PaperProofs
