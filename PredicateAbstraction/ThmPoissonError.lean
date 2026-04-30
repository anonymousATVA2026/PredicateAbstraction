import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem continuous_time_error_bound_poisson
    [Nonempty α]
    (P Ptilde : Matrix α α ℝ)
    (hP : CTMC.IsStochastic P)
    (hPtilde : CTMC.IsStochastic Ptilde)
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0)
    (r : NNReal) :
    l1Norm (fun i => ∑' n, ProbabilityTheory.poissonPMFReal r n
      * (vecIter v0 P n i - vecIter v0 Ptilde n i))
      ≤ (r : ℝ) * matrixInfNorm (errorMatrix P Ptilde)
 :=
  continuous_time_error_bound_poisson_core P Ptilde hP hPtilde v0 hv0 r

end PredicateAbstraction.CTMCFormalization
