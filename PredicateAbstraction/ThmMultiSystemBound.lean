import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Multivariate total error bound (same proof structure as the single-variable case). -/
theorem multivariateTotalErrorBound
    (Regions : Finset ι) (cells : ι → Finset α) (δ : ι → α → ℝ) (exitRate : α → ℝ)
    (rmin δInf : ι → ℝ)
    (hrmin : ∀ c ∈ Regions, 0 < rmin c)
    (hδ : ∀ c ∈ Regions, ∀ x ∈ cells c, |δ c x| ≤ δInf c)
    (hr_lower : ∀ c ∈ Regions, ∀ x ∈ cells c, rmin c ≤ exitRate x) :
    let totalErr : ℝ := ∑ c ∈ Regions, ∑ x ∈ cells c, δ c x * (1 / exitRate x)
    |totalErr| ≤ ∑ c ∈ Regions, δInf c * ((cells c).card : ℝ) / rmin c
 :=
  multivariateTotalErrorBound_core Regions cells δ exitRate rmin δInf hrmin hδ hr_lower

end PredicateAbstraction.PaperProofs
