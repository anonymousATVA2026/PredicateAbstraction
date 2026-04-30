import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Markov contraction: row-vector `L1` norm does not increase under a stochastic matrix. -/
theorem markov_contraction
    (P : Matrix α α ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j)
    (hP_row : ∀ i, (∑ j, P i j) = 1) :
    ∀ v : α → ℝ, l1Norm (vecMul v P) ≤ l1Norm v
 :=
  markov_contraction_core P hP_nonneg hP_row

end PredicateAbstraction.CTMCFormalization
