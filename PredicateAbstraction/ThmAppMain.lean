import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Generator-level continuous-time error bound for uniformization with common rate `γ`. -/
theorem continuous_time_error_bound_generators
    [Nonempty α]
    (C Ctilde : CTMC α)
    (γ t : NNReal)
    (hγpos : 0 < (γ : ℝ))
    (hγbound : ∀ i, C.exitRate i ≤ (γ : ℝ))
    (hγbound_tilde : ∀ i, Ctilde.exitRate i ≤ (γ : ℝ))
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0) :
    l1Norm (fun i => ∑' n, ProbabilityTheory.poissonPMFReal (γ * t) n
      * (vecIter v0 (C.uniformized (γ : ℝ)) n i - vecIter v0 (Ctilde.uniformized (γ : ℝ)) n i))
      ≤ (t : ℝ) * matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j)
 :=
  continuous_time_error_bound_generators_core C Ctilde γ t hγpos hγbound hγbound_tilde v0 hv0

end PredicateAbstraction.CTMCFormalization
