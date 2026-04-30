import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Infinite weighted version of the `n`-step error estimate. -/
theorem weighted_nStep_error_bound
    [Nonempty α]
    (w : ℕ → ℝ)
    (d : ℕ → α → ℝ)
    (B : ℝ)
    (hw_nonneg : ∀ n, 0 ≤ w n)
    (hbound : ∀ n, l1Norm (d n) ≤ (n : ℝ) * B)
    (hwmoment : Summable (fun n => w n * (n : ℝ))) :
    l1Norm (fun i => ∑' n, w n * d n i)
      ≤ (∑' n, w n * (n : ℝ)) * B
 :=
  weighted_nStep_error_bound_core w d B hw_nonneg hbound hwmoment

end PredicateAbstraction.CTMCFormalization
