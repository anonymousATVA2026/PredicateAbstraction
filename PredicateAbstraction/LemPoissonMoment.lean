import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem poissonPMFReal_firstMoment_tsum (r : NNReal) :
    (∑' n : ℕ, ProbabilityTheory.poissonPMFReal r n * (n : ℝ)) = (r : ℝ)
 :=
  poissonPMFReal_firstMoment_tsum_core r

end PredicateAbstraction.CTMCFormalization
