import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Reachability-style corollary: projection to any target set is bounded by the `L1` error. -/
theorem reachability_error_bound_generators
    [Nonempty α]
    (C Ctilde : CTMC α)
    (γ t : NNReal)
    (hγpos : 0 < (γ : ℝ))
    (hγbound : ∀ i, C.exitRate i ≤ (γ : ℝ))
    (hγbound_tilde : ∀ i, Ctilde.exitRate i ≤ (γ : ℝ))
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0)
    (F : Finset α) :
    let diff : α → ℝ :=
      fun i => ∑' n, ProbabilityTheory.poissonPMFReal (γ * t) n
        * (vecIter v0 (C.uniformized (γ : ℝ)) n i - vecIter v0 (Ctilde.uniformized (γ : ℝ)) n i)
    |∑ i ∈ F, diff i| ≤ (t : ℝ) * matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j)
 :=
  reachability_error_bound_generators_core C Ctilde γ t hγpos hγbound hγbound_tilde v0 hv0 F

end PredicateAbstraction.CTMCFormalization
