import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Single-variable total error bound across interval partitions, with each per-region
δ-norm given by `deviationNorm`. The right-hand sum ranges over `J.attach` so that the
nonempty proof `j.property` is available for each region. -/
theorem singleVariableTotalErrorBound
    (J : Finset ι) (I : ι → Finset α) (hI : ∀ j ∈ J, (I j).Nonempty)
    (δ : ι → α → ℝ) (r : α → ℝ)
    (rmin : ι → ℝ)
    (hrmin : ∀ j ∈ J, 0 < rmin j)
    (hr_lower : ∀ j ∈ J, ∀ x ∈ I j, rmin j ≤ r x) :
    let totalErr : ℝ := ∑ j ∈ J, ∑ x ∈ I j, δ j x * (1 / r x)
    |totalErr| ≤ ∑ j ∈ J.attach,
      deviationNorm (I j.val) (hI j.val j.property) (δ j.val)
        * ((I j.val).card : ℝ) / rmin j.val
 :=
  singleVariableTotalErrorBound_supNorm_core J I hI δ r rmin hrmin hr_lower

end PredicateAbstraction.PaperProofs
