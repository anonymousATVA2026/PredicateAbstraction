import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.PaperProofs

open Finset

variable {α ι : Type*}

/-- Deviation between any concrete rate `x = r_{k→ℓ}(i)` and the harmonic-mean abstract rate
`rHat = ((1/|I|)·∑ 1/r(y))⁻¹` is bounded by `rmax·(V-1)/V`. The fact that the harmonic mean
lies in `[rmin, rmax]` is supplied internally by `harmonicMean_in_interval_core`. -/
theorem deviationBoundFromVariationRatio
    (I : Finset α) (hI : I.Nonempty) (r : α → ℝ) (x rmin rmax V : ℝ)
    (hrmin : 0 < rmin)
    (hr_lower : ∀ y ∈ I, rmin ≤ r y)
    (hr_upper : ∀ y ∈ I, r y ≤ rmax)
    (hx_lower : rmin ≤ x)
    (hx_upper : x ≤ rmax)
    (hV : V = rmax / rmin) :
    let avgInv := (1 / (I.card : ℝ)) * (∑ y ∈ I, (1 / r y))
    let rHat : ℝ := avgInv⁻¹
    |x - rHat| ≤ rmax * (V - 1) / V
 :=
  harmonicMean_deviationBound_core I hI r x rmin rmax V hrmin hr_lower hr_upper
    hx_lower hx_upper hV

end PredicateAbstraction.PaperProofs
