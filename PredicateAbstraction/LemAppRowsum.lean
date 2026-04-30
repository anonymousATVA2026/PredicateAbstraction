import PredicateAbstraction.Defs

set_option linter.unusedSectionVars false

namespace PredicateAbstraction.CTMCFormalization

open Finset Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma errorMatrix_row_sum_zero
    {P Ptilde : Matrix α α ℝ}
    (hP_row : ∀ i, (∑ j, P i j) = 1)
    (hPtilde_row : ∀ i, (∑ j, Ptilde i j) = 1) :
    ∀ i, (∑ j, errorMatrix P Ptilde i j) = 0
 :=
  errorMatrix_row_sum_zero_core hP_row hPtilde_row

end PredicateAbstraction.CTMCFormalization
