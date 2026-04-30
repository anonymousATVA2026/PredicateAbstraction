import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Lifted matrix is stochastic when the abstract matrix is stochastic and `αmap` is surjective. -/
theorem lifted_isStochastic
    (αmap : α → β) (hsurj : Function.Surjective αmap) (Phat : Matrix β β ℝ)
    (hPhat : CTMC.IsStochastic Phat) :
    CTMC.IsStochastic (lifted αmap Phat)
 :=
  lifted_isStochastic_core αmap hsurj Phat hPhat

end PredicateAbstraction.CTMCFormalization
