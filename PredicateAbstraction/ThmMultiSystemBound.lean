import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Multivariate total error bound (rectangular partition in the paper), with each per-region
δ-norm given by `deviationNorm`. The right-hand sum ranges over `Regions.attach`. -/
theorem multivariateTotalErrorBound
    (Regions : Finset ι) (cells : ι → Finset α)
    (hCells : ∀ c ∈ Regions, (cells c).Nonempty)
    (δ : ι → α → ℝ) (exitRate : α → ℝ)
    (rmin : ι → ℝ)
    (hrmin : ∀ c ∈ Regions, 0 < rmin c)
    (hr_lower : ∀ c ∈ Regions, ∀ x ∈ cells c, rmin c ≤ exitRate x) :
    let totalErr : ℝ := ∑ c ∈ Regions, ∑ x ∈ cells c, δ c x * (1 / exitRate x)
    |totalErr| ≤ ∑ c ∈ Regions.attach,
      deviationNorm (cells c.val) (hCells c.val c.property) (δ c.val)
        * ((cells c.val).card : ℝ) / rmin c.val
 :=
  multivariateTotalErrorBound_supNorm_core Regions cells hCells δ exitRate rmin hrmin hr_lower

end PredicateAbstraction.PaperProofs
