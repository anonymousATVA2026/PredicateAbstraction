import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Variation-ratio explicit bound with off-diagonal aggregation derived from structural
block assumptions (intra-block cancellation, sign coherence, block-sum identity). -/
theorem explicit_reachability_error_bound_from_variation_ratio_sign_coherent
    [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (C Ctilde : CTMC α)
    (γ t : NNReal)
    (hγpos : 0 < (γ : ℝ))
    (hγbound : ∀ i, C.exitRate i ≤ (γ : ℝ))
    (hγbound_tilde : ∀ i, Ctilde.exitRate i ≤ (γ : ℝ))
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0)
    (F : Finset α)
    (αmap : α → β)
    (r : α → β → ℝ)
    (rHat : β → β → ℝ)
    (rmin rmax V : β → β → ℝ)
    (hIntraZero :
      ∀ i j, j ≠ i → αmap j = αmap i → C.Q i j - Ctilde.Q i j = 0)
    (hSign :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        (∀ j, αmap j = ℓ → 0 ≤ C.Q i j - Ctilde.Q i j) ∨
          (∀ j, αmap j = ℓ → C.Q i j - Ctilde.Q i j ≤ 0))
    (hBlockSum :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        (∑ j ∈ (univ.erase i) with αmap j = ℓ, (C.Q i j - Ctilde.Q i j))
          = r i ℓ - rHat (αmap i) ℓ)
    (hrBounds :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        rmin (αmap i) ℓ ≤ r i ℓ ∧ r i ℓ ≤ rmax (αmap i) ℓ)
    (hrHatBounds :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        rmin (αmap i) ℓ ≤ rHat (αmap i) ℓ ∧ rHat (αmap i) ℓ ≤ rmax (αmap i) ℓ)
    (hrminPos :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) → 0 < rmin (αmap i) ℓ)
    (hVdef : ∀ k ℓ, V k ℓ = rmax k ℓ / rmin k ℓ) :
    let term : β → β → ℝ := fun k ℓ => rmax k ℓ * (V k ℓ - 1) / V k ℓ
    let diff : α → ℝ :=
      fun i => ∑' n, ProbabilityTheory.poissonPMFReal (γ * t) n
        * (vecIter v0 (C.uniformized (γ : ℝ)) n i - vecIter v0 (Ctilde.uniformized (γ : ℝ)) n i)
    |∑ i ∈ F, diff i| ≤ 2 * (t : ℝ) * blockVariationBudget term
 :=
  explicit_reachability_error_bound_from_variation_ratio_sign_coherent_core C Ctilde γ t hγpos hγbound hγbound_tilde v0 hv0 F αmap r rHat rmin rmax V hIntraZero hSign hBlockSum hrBounds hrHatBounds hrminPos hVdef

end PredicateAbstraction.CTMCFormalization
