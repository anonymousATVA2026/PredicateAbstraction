import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Discrete-time error accumulation bound for two stochastic kernels. -/
theorem nStep_error_bound
    [Nonempty α]
    (P Ptilde : Matrix α α ℝ)
    (hP : CTMC.IsStochastic P)
    (hPtilde : CTMC.IsStochastic Ptilde)
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0) :
    ∀ n, l1Norm (fun j => vecIter v0 P n j - vecIter v0 Ptilde n j)
      ≤ (n : ℝ) * matrixInfNorm (errorMatrix P Ptilde)
 :=
  nStep_error_bound_core P Ptilde hP hPtilde v0 hv0

end PredicateAbstraction.CTMCFormalization
