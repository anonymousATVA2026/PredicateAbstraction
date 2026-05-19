import Mathlib

open scoped BigOperators

namespace PredicateAbstraction
namespace PaperProofs
open Finset

variable {α ι : Type*}

/-- Finite-set sup norm used as `‖δ‖∞` on an abstract region. -/
def deviationNorm (I : Finset α) (hI : I.Nonempty) (δ : α → ℝ) : ℝ :=
  I.sup' hI (fun x => |δ x|)

lemma deviationNorm_nonneg (I : Finset α) (hI : I.Nonempty) (δ : α → ℝ) :
    0 ≤ deviationNorm I hI δ := by
  have hle :
      |δ hI.choose| ≤ deviationNorm I hI δ :=
    Finset.le_sup' (f := fun x => |δ x|) hI.choose_spec
  exact le_trans (abs_nonneg _) hle

lemma abs_le_deviationNorm (I : Finset α) (hI : I.Nonempty) (δ : α → ℝ)
    {x : α} (hx : x ∈ I) :
    |δ x| ≤ deviationNorm I hI δ := by
  exact Finset.le_sup' (f := fun y => |δ y|) hx

/-- Expected residence time under uniform entry on a finite abstract region. -/
theorem expectedResidence_uniform
    (I : Finset α) (p r : α → ℝ)
    (hp : ∀ x ∈ I, p x = 1 / (I.card : ℝ)) :
    (∑ x ∈ I, p x * (1 / r x)) =
      (1 / (I.card : ℝ)) * (∑ x ∈ I, (1 / r x)) := by
  calc
    ∑ x ∈ I, p x * (1 / r x)
        = ∑ x ∈ I, (1 / (I.card : ℝ)) * (1 / r x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [hp x hx]
    _ = (1 / (I.card : ℝ)) * (∑ x ∈ I, (1 / r x)) := by
          rw [Finset.mul_sum]

/-- Harmonic-mean aggregation preserves expected residence time. -/
theorem harmonicMeanAggregation_core
    (I : Finset α) (hI : I.Nonempty) (r : α → ℝ)
    (hr : ∀ x ∈ I, 0 < r x) :
    let avgInv := (1 / (I.card : ℝ)) * (∑ x ∈ I, (1 / r x))
    let rHat : ℝ := avgInv⁻¹
    1 / rHat = avgInv := by
  intro avgInv rHat
  have hcard_pos : 0 < (I.card : ℝ) := by
    exact Nat.cast_pos.mpr hI.card_pos
  have hsum_pos : 0 < ∑ x ∈ I, (1 / r x) := by
    refine Finset.sum_pos' ?h_nonneg ?h_strict
    · intro x hx
      exact le_of_lt (one_div_pos.mpr (hr x hx))
    · refine ⟨hI.choose, hI.choose_spec, ?_⟩
      exact one_div_pos.mpr (hr hI.choose hI.choose_spec)
  have havg_pos : 0 < avgInv := by
    dsimp [avgInv]
    exact mul_pos (one_div_pos.mpr hcard_pos) hsum_pos
  simp [rHat, avgInv]

/-- Single-interval error bound with an explicit `δInf` satisfying `|δ| ≤ δInf`. -/
theorem errorBoundNonUniformEntry
    (I : Finset α) (δ r : α → ℝ) (rmin δInf : ℝ)
    (hrmin : 0 < rmin)
    (hδ : ∀ x ∈ I, |δ x| ≤ δInf)
    (hr_lower : ∀ x ∈ I, rmin ≤ r x) :
    let err : ℝ := ∑ x ∈ I, δ x * (1 / r x)
    |err| ≤ δInf * (I.card : ℝ) / rmin := by
  intro err
  have hterm :
      ∀ x ∈ I, |δ x * (1 / r x)| ≤ δInf * (1 / rmin) := by
    intro x hx
    have hδx : |δ x| ≤ δInf := hδ x hx
    have hrx : rmin ≤ r x := hr_lower x hx
    have hrx_pos : 0 < r x := lt_of_lt_of_le hrmin hrx
    have hinv_nonneg : 0 ≤ 1 / r x := le_of_lt (one_div_pos.mpr hrx_pos)
    have hδinf_nonneg : 0 ≤ δInf := by
      exact le_trans (abs_nonneg (δ x)) hδx
    have hinv_le : 1 / r x ≤ 1 / rmin := by
      exact one_div_le_one_div_of_le hrmin hrx
    calc
      |δ x * (1 / r x)| = |δ x| * (1 / r x) := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hrx_pos)]
      _ ≤ δInf * (1 / r x) := by
        exact mul_le_mul_of_nonneg_right hδx hinv_nonneg
      _ ≤ δInf * (1 / rmin) := by
        exact mul_le_mul_of_nonneg_left hinv_le hδinf_nonneg
  have hsum :
      ∑ x ∈ I, |δ x * (1 / r x)| ≤ ∑ x ∈ I, δInf * (1 / rmin) := by
    exact Finset.sum_le_sum (by intro x hx; exact hterm x hx)
  calc
    |err| = |∑ x ∈ I, δ x * (1 / r x)| := rfl
    _ ≤ ∑ x ∈ I, |δ x * (1 / r x)| := by
      simpa using (abs_sum_le_sum_abs (s := I) (f := fun x => δ x * (1 / r x)))
    _ ≤ ∑ x ∈ I, δInf * (1 / rmin) := hsum
    _ = (I.card : ℝ) * (δInf * (1 / rmin)) := by simp
    _ = δInf * (I.card : ℝ) / rmin := by ring

/-- The paper's single-interval bound using `deviationNorm = ‖δ‖∞`. -/
theorem errorBoundNonUniformEntry_supNorm_core
    (I : Finset α) (hI : I.Nonempty) (δ r : α → ℝ) (rmin : ℝ)
    (hrmin : 0 < rmin)
    (hr_lower : ∀ x ∈ I, rmin ≤ r x) :
    let err : ℝ := ∑ x ∈ I, δ x * (1 / r x)
    |err| ≤ deviationNorm I hI δ * (I.card : ℝ) / rmin := by
  intro err
  exact errorBoundNonUniformEntry
    (I := I) (δ := δ) (r := r) (rmin := rmin) (δInf := deviationNorm I hI δ)
    hrmin (fun x hx => abs_le_deviationNorm I hI δ hx) hr_lower

/-- Single-variable total error bound across interval partitions. -/
theorem singleVariableTotalErrorBound_core
    (J : Finset ι) (I : ι → Finset α) (δ : ι → α → ℝ) (r : α → ℝ)
    (rmin δInf : ι → ℝ)
    (hrmin : ∀ j ∈ J, 0 < rmin j)
    (hδ : ∀ j ∈ J, ∀ x ∈ I j, |δ j x| ≤ δInf j)
    (hr_lower : ∀ j ∈ J, ∀ x ∈ I j, rmin j ≤ r x) :
    let totalErr : ℝ := ∑ j ∈ J, ∑ x ∈ I j, δ j x * (1 / r x)
    |totalErr| ≤ ∑ j ∈ J, δInf j * ((I j).card : ℝ) / rmin j := by
  intro totalErr
  have hinner :
      ∀ j ∈ J, |∑ x ∈ I j, δ j x * (1 / r x)| ≤ δInf j * ((I j).card : ℝ) / rmin j := by
    intro j hj
    exact errorBoundNonUniformEntry
      (I := I j) (δ := δ j) (r := r) (rmin := rmin j) (δInf := δInf j)
      (hrmin j hj) (hδ j hj) (hr_lower j hj)
  calc
    |totalErr| = |∑ j ∈ J, ∑ x ∈ I j, δ j x * (1 / r x)| := rfl
    _ ≤ ∑ j ∈ J, |∑ x ∈ I j, δ j x * (1 / r x)| := by
      simpa using
        (abs_sum_le_sum_abs (s := J) (f := fun j => ∑ x ∈ I j, δ j x * (1 / r x)))
    _ ≤ ∑ j ∈ J, δInf j * ((I j).card : ℝ) / rmin j := by
      exact Finset.sum_le_sum (by intro j hj; exact hinner j hj)

/-- Multivariate total error bound (same proof structure as the single-variable case). -/
theorem multivariateTotalErrorBound_core
    (Regions : Finset ι) (cells : ι → Finset α) (δ : ι → α → ℝ) (exitRate : α → ℝ)
    (rmin δInf : ι → ℝ)
    (hrmin : ∀ c ∈ Regions, 0 < rmin c)
    (hδ : ∀ c ∈ Regions, ∀ x ∈ cells c, |δ c x| ≤ δInf c)
    (hr_lower : ∀ c ∈ Regions, ∀ x ∈ cells c, rmin c ≤ exitRate x) :
    let totalErr : ℝ := ∑ c ∈ Regions, ∑ x ∈ cells c, δ c x * (1 / exitRate x)
    |totalErr| ≤ ∑ c ∈ Regions, δInf c * ((cells c).card : ℝ) / rmin c := by
  intro totalErr
  exact singleVariableTotalErrorBound_core
    (J := Regions) (I := cells) (δ := δ) (r := exitRate)
    (rmin := rmin) (δInf := δInf) hrmin hδ hr_lower

/-- Variation-error correspondence from the refinement section. -/
theorem variationErrorCorrespondence_core
    (err δInf regionSize rmax rmin V : ℝ)
    (hbound : |err| ≤ δInf * regionSize / rmin)
    (hV : V = rmax / rmin)
    (hrmin : 0 < rmin) (hrmax : 0 < rmax) :
    |err| ≤ δInf * regionSize * V / rmax := by
  have hratio : V / rmax = 1 / rmin := by
    rw [hV]
    field_simp [hrmin.ne', hrmax.ne']
  have hEq : δInf * regionSize * V / rmax = δInf * regionSize / rmin := by
    calc
      δInf * regionSize * V / rmax = δInf * regionSize * (V / rmax) := by ring
      _ = δInf * regionSize * (1 / rmin) := by rw [hratio]
      _ = δInf * regionSize / rmin := by ring
  simpa [hEq] using hbound

/-- Interval deviation bound in variation-ratio form. -/
theorem deviationBoundFromVariationRatio_core
    (x xhat rmin rmax V : ℝ)
    (hx_lower : rmin ≤ x)
    (hx_upper : x ≤ rmax)
    (hxhat_lower : rmin ≤ xhat)
    (hxhat_upper : xhat ≤ rmax)
    (hrmin : 0 < rmin)
    (hV : V = rmax / rmin) :
    |x - xhat| ≤ rmax * (V - 1) / V := by
  have hdiff_upper : x - xhat ≤ rmax - rmin := by
    exact sub_le_sub hx_upper hxhat_lower
  have hdiff_upper_symm : xhat - x ≤ rmax - rmin := by
    exact sub_le_sub hxhat_upper hx_lower
  have hdiff_lower : -(rmax - rmin) ≤ x - xhat := by
    linarith
  have habs : |x - xhat| ≤ rmax - rmin := by
    exact abs_le.mpr ⟨hdiff_lower, hdiff_upper⟩
  have hrmax : 0 < rmax := by
    exact lt_of_lt_of_le hrmin (le_trans hx_lower hx_upper)
  have hEq : rmax - rmin = rmax * (V - 1) / V := by
    rw [hV]
    field_simp [hrmin.ne', hrmax.ne']
  calc
    |x - xhat| ≤ rmax - rmin := habs
    _ = rmax * (V - 1) / V := hEq

/-- Temporal preservation: under uniform entry on `I`, the expected residence time
`∑ p(x)·1/r(x)` equals `1/rHat` where `rHat` is the harmonic-mean rate. -/
theorem harmonicMean_temporalPreservation_core
    (I : Finset α) (hI : I.Nonempty) (r p : α → ℝ)
    (hr : ∀ x ∈ I, 0 < r x)
    (hp : ∀ x ∈ I, p x = 1 / (I.card : ℝ)) :
    let avgInv := (1 / (I.card : ℝ)) * (∑ x ∈ I, (1 / r x))
    let rHat : ℝ := avgInv⁻¹
    (∑ x ∈ I, p x * (1 / r x)) = 1 / rHat := by
  intro avgInv rHat
  have h1 :
      (∑ x ∈ I, p x * (1 / r x)) = avgInv :=
    expectedResidence_uniform (I := I) (p := p) (r := r) hp
  have h2 : (1 / rHat) = avgInv :=
    harmonicMeanAggregation_core (I := I) (hI := hI) (r := r) hr
  rw [h1, h2]

/-- Lower bound on the harmonic mean: if every `r x` lies in `[rmin, rmax]` with `rmin > 0`,
then so does `rHat := ((1/|I|)·∑ 1/r x)⁻¹`. -/
theorem harmonicMean_in_interval_core
    (I : Finset α) (hI : I.Nonempty) (r : α → ℝ) (rmin rmax : ℝ)
    (hrmin_pos : 0 < rmin)
    (hr_lower : ∀ x ∈ I, rmin ≤ r x)
    (hr_upper : ∀ x ∈ I, r x ≤ rmax) :
    let avgInv := (1 / (I.card : ℝ)) * (∑ x ∈ I, (1 / r x))
    let rHat : ℝ := avgInv⁻¹
    rmin ≤ rHat ∧ rHat ≤ rmax := by
  intro avgInv rHat
  have hcard_pos : 0 < (I.card : ℝ) := Nat.cast_pos.mpr hI.card_pos
  have hrx_pos : ∀ x ∈ I, 0 < r x := fun x hx => lt_of_lt_of_le hrmin_pos (hr_lower x hx)
  have hrmax_pos : 0 < rmax := by
    rcases hI with ⟨x, hx⟩
    exact lt_of_lt_of_le (hrx_pos x hx) (hr_upper x hx)
  -- Pointwise bounds on 1/r x.
  have hinv_lower : ∀ x ∈ I, 1 / rmax ≤ 1 / r x := fun x hx =>
    one_div_le_one_div_of_le (hrx_pos x hx) (hr_upper x hx)
  have hinv_upper : ∀ x ∈ I, 1 / r x ≤ 1 / rmin := fun x hx =>
    one_div_le_one_div_of_le hrmin_pos (hr_lower x hx)
  -- Sum bounds on ∑ 1/r x.
  have hsum_lower : ((I.card : ℝ)) * (1 / rmax) ≤ ∑ x ∈ I, 1 / r x := by
    calc ((I.card : ℝ)) * (1 / rmax)
        = ∑ _x ∈ I, (1 / rmax) := by
          simp [mul_comm]
      _ ≤ ∑ x ∈ I, 1 / r x :=
          Finset.sum_le_sum (fun x hx => hinv_lower x hx)
  have hsum_upper : (∑ x ∈ I, 1 / r x) ≤ ((I.card : ℝ)) * (1 / rmin) := by
    calc (∑ x ∈ I, 1 / r x)
        ≤ ∑ _x ∈ I, (1 / rmin) :=
          Finset.sum_le_sum (fun x hx => hinv_upper x hx)
      _ = ((I.card : ℝ)) * (1 / rmin) := by simp [mul_comm]
  -- avgInv bounds.
  have havgInv_lower : 1 / rmax ≤ avgInv := by
    dsimp [avgInv]
    have := mul_le_mul_of_nonneg_left hsum_lower
      (le_of_lt (one_div_pos.mpr hcard_pos))
    have hsimpl : (1 / (I.card : ℝ)) * ((I.card : ℝ) * (1 / rmax)) = 1 / rmax := by
      field_simp
    linarith
  have havgInv_upper : avgInv ≤ 1 / rmin := by
    dsimp [avgInv]
    have := mul_le_mul_of_nonneg_left hsum_upper
      (le_of_lt (one_div_pos.mpr hcard_pos))
    have hsimpl : (1 / (I.card : ℝ)) * ((I.card : ℝ) * (1 / rmin)) = 1 / rmin := by
      field_simp
    linarith
  have havg_pos : 0 < avgInv :=
    lt_of_lt_of_le (one_div_pos.mpr hrmax_pos) havgInv_lower
  -- Translate to rHat = avgInv⁻¹.
  refine ⟨?_, ?_⟩
  · -- rmin ≤ rHat: from avgInv ≤ 1/rmin take reciprocals.
    have : 1 / (1 / rmin) ≤ 1 / avgInv :=
      one_div_le_one_div_of_le havg_pos havgInv_upper
    have hrec : (1 / rmin)⁻¹ = rmin := by field_simp
    have hAvg : (1 / avgInv) = avgInv⁻¹ := by simp [one_div]
    have hRecAlt : (1 / (1 / rmin)) = rmin := by field_simp
    -- Conclude.
    simpa [rHat, hRecAlt, hAvg] using this
  · -- rHat ≤ rmax: from 1/rmax ≤ avgInv take reciprocals.
    have hrmax_inv_pos : 0 < 1 / rmax := one_div_pos.mpr hrmax_pos
    have : 1 / avgInv ≤ 1 / (1 / rmax) :=
      one_div_le_one_div_of_le hrmax_inv_pos havgInv_lower
    have hAvg : (1 / avgInv) = avgInv⁻¹ := by simp [one_div]
    have hRecAlt : (1 / (1 / rmax)) = rmax := by field_simp
    simpa [rHat, hRecAlt, hAvg] using this

/-- Single-variable total error bound using `deviationNorm = ‖δ‖∞` per region.
The sum on the right-hand side ranges over `J.attach`, which gives access to the membership
proof `j.property : j.val ∈ J` needed to apply `deviationNorm`. -/
theorem singleVariableTotalErrorBound_supNorm_core
    (J : Finset ι) (I : ι → Finset α) (hI : ∀ j ∈ J, (I j).Nonempty)
    (δ : ι → α → ℝ) (r : α → ℝ)
    (rmin : ι → ℝ)
    (hrmin : ∀ j ∈ J, 0 < rmin j)
    (hr_lower : ∀ j ∈ J, ∀ x ∈ I j, rmin j ≤ r x) :
    let totalErr : ℝ := ∑ j ∈ J, ∑ x ∈ I j, δ j x * (1 / r x)
    |totalErr| ≤ ∑ j ∈ J.attach,
      deviationNorm (I j.val) (hI j.val j.property) (δ j.val)
        * ((I j.val).card : ℝ) / rmin j.val := by
  intro totalErr
  -- Apply the per-interval supNorm bound and aggregate.
  have hinner :
      ∀ j ∈ J.attach,
        |∑ x ∈ I j.val, δ j.val x * (1 / r x)|
          ≤ deviationNorm (I j.val) (hI j.val j.property) (δ j.val)
              * ((I j.val).card : ℝ) / rmin j.val := by
    intro j hj
    have := errorBoundNonUniformEntry_supNorm_core
      (I := I j.val) (hI := hI j.val j.property)
      (δ := δ j.val) (r := r) (rmin := rmin j.val)
      (hrmin j.val j.property) (hr_lower j.val j.property)
    simpa using this
  have hsum_eq :
      (∑ j ∈ J, ∑ x ∈ I j, δ j x * (1 / r x))
        = ∑ j ∈ J.attach, ∑ x ∈ I j.val, δ j.val x * (1 / r x) := by
    rw [← Finset.sum_attach (s := J) (f := fun j => ∑ x ∈ I j, δ j x * (1 / r x))]
  calc
    |totalErr|
        = |∑ j ∈ J.attach, ∑ x ∈ I j.val, δ j.val x * (1 / r x)| := by
          show |∑ j ∈ J, ∑ x ∈ I j, δ j x * (1 / r x)| = _
          rw [hsum_eq]
    _ ≤ ∑ j ∈ J.attach, |∑ x ∈ I j.val, δ j.val x * (1 / r x)| := by
          simpa using
            (abs_sum_le_sum_abs (s := J.attach)
              (f := fun j => ∑ x ∈ I j.val, δ j.val x * (1 / r x)))
    _ ≤ ∑ j ∈ J.attach,
          deviationNorm (I j.val) (hI j.val j.property) (δ j.val)
            * ((I j.val).card : ℝ) / rmin j.val :=
          Finset.sum_le_sum hinner

/-- Multivariate total error bound using `deviationNorm = ‖δ‖∞` per region. -/
theorem multivariateTotalErrorBound_supNorm_core
    (Regions : Finset ι) (cells : ι → Finset α)
    (hCells : ∀ c ∈ Regions, (cells c).Nonempty)
    (δ : ι → α → ℝ) (exitRate : α → ℝ)
    (rmin : ι → ℝ)
    (hrmin : ∀ c ∈ Regions, 0 < rmin c)
    (hr_lower : ∀ c ∈ Regions, ∀ x ∈ cells c, rmin c ≤ exitRate x) :
    let totalErr : ℝ := ∑ c ∈ Regions, ∑ x ∈ cells c, δ c x * (1 / exitRate x)
    |totalErr| ≤ ∑ c ∈ Regions.attach,
      deviationNorm (cells c.val) (hCells c.val c.property) (δ c.val)
        * ((cells c.val).card : ℝ) / rmin c.val := by
  intro totalErr
  exact singleVariableTotalErrorBound_supNorm_core
    (J := Regions) (I := cells) (hI := hCells) (δ := δ) (r := exitRate)
    (rmin := rmin) hrmin hr_lower

/-- Variation–error correspondence: derive the error bound from `errorBoundNonUniformEntry`
and reformulate via the variation ratio `V = rmax / rmin`. -/
theorem variationErrorCorrespondence_fromErrorBound_core
    (I : Finset α) (hI : I.Nonempty) (δ r : α → ℝ) (rmin rmax V : ℝ)
    (hrmin : 0 < rmin) (hrmax : 0 < rmax)
    (hr_lower : ∀ x ∈ I, rmin ≤ r x)
    (hV : V = rmax / rmin) :
    let err : ℝ := ∑ x ∈ I, δ x * (1 / r x)
    |err| ≤ deviationNorm I hI δ * ((I.card : ℝ)) * V / rmax := by
  intro err
  have hbase :
      |err| ≤ deviationNorm I hI δ * (I.card : ℝ) / rmin :=
    errorBoundNonUniformEntry_supNorm_core (I := I) (hI := hI) (δ := δ) (r := r)
      (rmin := rmin) hrmin hr_lower
  exact variationErrorCorrespondence_core
    (err := err)
    (δInf := deviationNorm I hI δ)
    (regionSize := (I.card : ℝ))
    (rmax := rmax) (rmin := rmin) (V := V)
    hbase hV hrmin hrmax

/-- Specialization of `deviationBoundFromVariationRatio_core` to the case where one of the
two values is the harmonic mean of `r` on `I` (which lies in `[rmin, rmax]` by
`harmonicMean_in_interval_core`). -/
theorem harmonicMean_deviationBound_core
    (I : Finset α) (hI : I.Nonempty) (r : α → ℝ) (x rmin rmax V : ℝ)
    (hrmin : 0 < rmin)
    (hr_lower : ∀ y ∈ I, rmin ≤ r y)
    (hr_upper : ∀ y ∈ I, r y ≤ rmax)
    (hx_lower : rmin ≤ x)
    (hx_upper : x ≤ rmax)
    (hV : V = rmax / rmin) :
    let avgInv := (1 / (I.card : ℝ)) * (∑ y ∈ I, (1 / r y))
    let rHat : ℝ := avgInv⁻¹
    |x - rHat| ≤ rmax * (V - 1) / V := by
  intro avgInv rHat
  obtain ⟨hrHat_lower, hrHat_upper⟩ :=
    harmonicMean_in_interval_core (I := I) (hI := hI) (r := r)
      (rmin := rmin) (rmax := rmax) hrmin hr_lower hr_upper
  exact deviationBoundFromVariationRatio_core
    (x := x) (xhat := rHat)
    (rmin := rmin) (rmax := rmax) (V := V)
    hx_lower hx_upper hrHat_lower hrHat_upper hrmin hV

/-- Error-bounded termination inequality from Theorem 6. -/
theorem errorBoundedTermination_core
    (ε T rmax V err : ℝ)
    (_hε : 0 < ε)
    (hε_lt : ε < 2 * T * rmax)
    (hVpos : 0 < V)
    (herr : |err| ≤ 2 * T * rmax * (V - 1) / V)
    (hV :
      V ≤ (2 * T * rmax) / (2 * T * rmax - ε)) :
    |err| ≤ ε := by
  let A : ℝ := 2 * T * rmax
  have hden : 0 < A - ε := by
    dsimp [A]
    linarith [hε_lt]
  have hVmul : V * (A - ε) ≤ A := by
    calc
      V * (A - ε) ≤ (A / (A - ε)) * (A - ε) := by
        exact mul_le_mul_of_nonneg_right hV (le_of_lt hden)
      _ = A := by
        field_simp [hden.ne']
  have hAineq : A * (V - 1) ≤ ε * V := by
    nlinarith [hVmul]
  have hfrac : A * (V - 1) / V ≤ ε := by
    exact (div_le_iff₀ hVpos).2 (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hAineq)
  have herrA : |err| ≤ A * (V - 1) / V := by
    simpa [A] using herr
  exact le_trans herrA hfrac


end PaperProofs

namespace CTMCFormalization
open Finset Matrix

variable {α β : Type*}

section FiniteState

variable [Fintype α] [DecidableEq α]

/-- Finite-state CTMC given by a generator matrix. -/
structure CTMC (α : Type*) [Fintype α] [DecidableEq α] where
  Q : Matrix α α ℝ
  offDiag_nonneg : ∀ i j, i ≠ j → 0 ≤ Q i j
  row_sum_zero : ∀ i, (∑ j, Q i j) = 0

namespace CTMC

/-- Exit rate as sum of off-diagonal rates from state `i`. -/
def exitRate (C : CTMC α) (i : α) : ℝ :=
  ∑ j ∈ ((univ : Finset α).erase i), C.Q i j

lemma exitRate_nonneg (C : CTMC α) (i : α) : 0 ≤ C.exitRate i := by
  refine sum_nonneg ?_
  intro j hj
  exact C.offDiag_nonneg i j (by simpa [ne_comm] using (Finset.ne_of_mem_erase hj))

lemma row_split (C : CTMC α) (i : α) :
    (∑ j, C.Q i j) = C.Q i i + C.exitRate i := by
  classical
  calc
    (∑ j, C.Q i j) = (∑ j ∈ (univ : Finset α).erase i, C.Q i j) + C.Q i i := by
      exact (Finset.sum_erase_add (s := (univ : Finset α)) (a := i) (f := fun j => C.Q i j)
        (Finset.mem_univ i)).symm
    _ = C.Q i i + C.exitRate i := by
      rw [CTMC.exitRate, add_comm]

lemma diag_eq_neg_exitRate (C : CTMC α) (i : α) :
    C.Q i i = -C.exitRate i := by
  have h := C.row_sum_zero i
  rw [C.row_split i] at h
  linarith

/-- Uniformized discrete-time transition matrix for rate `γ`. -/
noncomputable def uniformized (C : CTMC α) (γ : ℝ) : Matrix α α ℝ :=
  fun i j => if i = j then 1 - C.exitRate i / γ else C.Q i j / γ

/-- Stochastic matrix predicate (nonnegative entries, rows sum to 1). -/
def IsStochastic (P : Matrix α α ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∀ i, (∑ j, P i j) = 1)

lemma uniformized_nonneg (C : CTMC α) {γ : ℝ}
    (hγpos : 0 < γ) (hγbound : ∀ i, C.exitRate i ≤ γ) :
    ∀ i j, 0 ≤ C.uniformized γ i j := by
  intro i j
  by_cases h : i = j
  · subst h
    simp [uniformized]
    have hdiv : C.exitRate i / γ ≤ 1 := by
      have hγnonneg : 0 ≤ γ := le_of_lt hγpos
      have htmp : C.exitRate i / γ ≤ γ / γ := div_le_div_of_nonneg_right (hγbound i) hγnonneg
      simpa [hγpos.ne'] using htmp
    linarith
  · simp [uniformized, h]
    exact div_nonneg (C.offDiag_nonneg i j h) (le_of_lt hγpos)

lemma uniformized_row_sum (C : CTMC α) {γ : ℝ} (_hγpos : 0 < γ) :
    ∀ i, (∑ j, C.uniformized γ i j) = 1 := by
  intro i
  have hsplit :
      (∑ j, C.uniformized γ i j) =
        C.uniformized γ i i + ∑ j ∈ univ.erase i, C.uniformized γ i j := by
    calc
      (∑ j, C.uniformized γ i j) =
          (∑ j ∈ univ.erase i, C.uniformized γ i j) + C.uniformized γ i i := by
            exact (Finset.sum_erase_add (s := (univ : Finset α)) (a := i)
              (f := fun j => C.uniformized γ i j) (Finset.mem_univ i)).symm
      _ = C.uniformized γ i i + ∑ j ∈ univ.erase i, C.uniformized γ i j := by
            rw [add_comm]
  rw [hsplit]
  have hdiag : C.uniformized γ i i = 1 - C.exitRate i / γ := by
    simp [uniformized]
  have hoff :
      (∑ j ∈ univ.erase i, C.uniformized γ i j) =
        (∑ j ∈ univ.erase i, C.Q i j / γ) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hij : i ≠ j := by
      simpa [ne_comm] using (Finset.ne_of_mem_erase hj)
    simp [uniformized, hij]
  have hsum_div :
      (∑ j ∈ univ.erase i, C.Q i j / γ) = C.exitRate i / γ := by
    unfold CTMC.exitRate
    rw [Finset.sum_div]
  rw [hdiag, hoff, hsum_div]
  ring

theorem uniformized_isStochastic (C : CTMC α) {γ : ℝ}
    (hγpos : 0 < γ) (hγbound : ∀ i, C.exitRate i ≤ γ) :
    IsStochastic (C.uniformized γ) := by
  refine ⟨C.uniformized_nonneg hγpos hγbound, C.uniformized_row_sum hγpos⟩

end CTMC

/-- Block induced by an abstraction function. -/
def block [DecidableEq β] (αmap : α → β) (k : β) : Finset α :=
  univ.filter (fun i => αmap i = k)

section Lifted

variable [Fintype β] [DecidableEq β]

/-- Lifted abstract stochastic matrix on concrete states. -/
noncomputable def lifted (αmap : α → β) (Phat : Matrix β β ℝ) : Matrix α α ℝ :=
  fun i j => Phat (αmap i) (αmap j) / ((block αmap (αmap j)).card : ℝ)

omit [DecidableEq α] [Fintype β] in
lemma block_card_pos_of_mem (αmap : α → β) (j : α) :
    0 < (block αmap (αmap j)).card := by
  refine Finset.card_pos.mpr ?_
  exact ⟨j, by simp [block]⟩

omit [DecidableEq α] [Fintype β] in
lemma block_card_pos_of_surjective (αmap : α → β) (hsurj : Function.Surjective αmap) (k : β) :
    0 < (block αmap k).card := by
  rcases hsurj k with ⟨j, rfl⟩
  exact block_card_pos_of_mem αmap j

omit [DecidableEq α] [Fintype β] in
theorem lifted_nonneg
    (αmap : α → β) (Phat : Matrix β β ℝ)
    (hPhat_nonneg : ∀ i j, 0 ≤ Phat i j) :
    ∀ i j, 0 ≤ lifted αmap Phat i j := by
  intro i j
  have hcard : 0 < ((block αmap (αmap j)).card : ℝ) := by
    exact Nat.cast_pos.mpr (block_card_pos_of_mem αmap j)
  exact div_nonneg (hPhat_nonneg _ _) (le_of_lt hcard)

omit [DecidableEq α] in
theorem lifted_row_sum
    (αmap : α → β) (hsurj : Function.Surjective αmap) (Phat : Matrix β β ℝ)
    (hPhat_row : ∀ k, (∑ ℓ, Phat k ℓ) = 1) :
    ∀ i, (∑ j, lifted αmap Phat i j) = 1 := by
  intro i
  have hmaps : ∀ j ∈ (univ : Finset α), αmap j ∈ (univ : Finset β) := by
    intro j hj
    simp
  calc
    (∑ j, lifted αmap Phat i j)
        = ∑ ℓ, ∑ j ∈ (univ : Finset α) with αmap j = ℓ,
            (Phat (αmap i) (αmap j) / ((block αmap (αmap j)).card : ℝ)) := by
              simpa [lifted] using
                (Finset.sum_fiberwise_of_maps_to (s := (univ : Finset α)) (t := (univ : Finset β))
                  (g := αmap) hmaps
                  (f := fun j => Phat (αmap i) (αmap j) / ((block αmap (αmap j)).card : ℝ))).symm
    _ = ∑ ℓ, ∑ j ∈ (univ : Finset α) with αmap j = ℓ,
          (Phat (αmap i) ℓ / ((block αmap ℓ).card : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro ℓ hℓ
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp at hj
            simp [hj]
    _ = ∑ ℓ, ((block αmap ℓ).card : ℝ) * (Phat (αmap i) ℓ / ((block αmap ℓ).card : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro ℓ hℓ
          simp [block]
    _ = ∑ ℓ, Phat (αmap i) ℓ := by
          refine Finset.sum_congr rfl ?_
          intro ℓ hℓ
          have hposNat : 0 < (block αmap ℓ).card := block_card_pos_of_surjective αmap hsurj ℓ
          have hpos : 0 < ((block αmap ℓ).card : ℝ) := Nat.cast_pos.mpr hposNat
          field_simp [hpos.ne']
    _ = 1 := hPhat_row (αmap i)

omit [DecidableEq α] in
/-- Lifted matrix is stochastic when the abstract matrix is stochastic and `αmap` is surjective. -/
theorem lifted_isStochastic_core
    (αmap : α → β) (hsurj : Function.Surjective αmap) (Phat : Matrix β β ℝ)
    (hPhat : CTMC.IsStochastic Phat) :
    CTMC.IsStochastic (lifted αmap Phat) := by
  refine ⟨lifted_nonneg αmap Phat hPhat.1, lifted_row_sum αmap hsurj Phat hPhat.2⟩

end Lifted

section ErrorAndContraction

/-- `L1` norm on finite real-valued vectors. -/
def l1Norm (v : α → ℝ) : ℝ := ∑ i, |v i|

omit [DecidableEq α] in
lemma l1Norm_nonneg (v : α → ℝ) : 0 ≤ l1Norm v := by
  unfold l1Norm
  exact Finset.sum_nonneg (fun i hi => abs_nonneg (v i))

omit [DecidableEq α] in
lemma abs_le_l1Norm (v : α → ℝ) (i : α) : |v i| ≤ l1Norm v := by
  unfold l1Norm
  exact Finset.single_le_sum (fun j hj => abs_nonneg (v j)) (by simp)

/-- Row-vector multiplication by a matrix. -/
def vecMul (v : α → ℝ) (P : Matrix α α ℝ) : α → ℝ :=
  fun j => ∑ i, v i * P i j

/-- Iterated row-vector dynamics under a stochastic matrix. -/
def vecIter (v : α → ℝ) (P : Matrix α α ℝ) : ℕ → (α → ℝ)
  | 0 => v
  | n + 1 => vecMul (vecIter v P n) P

/-- Error matrix between two stochastic matrices. -/
def errorMatrix (P Ptilde : Matrix α α ℝ) : Matrix α α ℝ :=
  P - Ptilde

/-- Probability distribution on a finite state space. -/
def IsDistribution (v : α → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ ((∑ i, v i) = 1)

/-- Matrix `∞`-norm as maximal absolute row sum. -/
noncomputable def matrixInfNorm [Nonempty α] (A : Matrix α α ℝ) : ℝ :=
  by
    classical
    exact ((univ : Finset α).image (fun i => ∑ j, |A i j|)).max' (by
      rcases (show Nonempty α from inferInstance) with ⟨i⟩
      exact ⟨∑ j, |A i j|, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)

omit [DecidableEq α] in
lemma l1Norm_add_le (v w : α → ℝ) :
    l1Norm (fun i => v i + w i) ≤ l1Norm v + l1Norm w := by
  unfold l1Norm
  calc
    (∑ i, |v i + w i|) ≤ ∑ i, (|v i| + |w i|) := by
      exact Finset.sum_le_sum (fun i hi => abs_add_le (v i) (w i))
    _ = (∑ i, |v i|) + (∑ i, |w i|) := by
      rw [Finset.sum_add_distrib]

omit [DecidableEq α] in
lemma vecMul_sub_left (v w : α → ℝ) (P : Matrix α α ℝ) :
    (fun j => vecMul v P j - vecMul w P j) = vecMul (fun i => v i - w i) P := by
  funext j
  simp [vecMul, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq α] in
lemma vecMul_sub_right (v : α → ℝ) (P Q : Matrix α α ℝ) :
    (fun j => vecMul v P j - vecMul v Q j) = vecMul v (P - Q) := by
  funext j
  simp [vecMul, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq α] in
lemma vecMul_nonneg
    (v : α → ℝ) (P : Matrix α α ℝ)
    (hv_nonneg : ∀ i, 0 ≤ v i)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) :
    ∀ j, 0 ≤ vecMul v P j := by
  intro j
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hv_nonneg i) (hP_nonneg i j))

omit [DecidableEq α] in
lemma vecMul_sum
    (v : α → ℝ) (P : Matrix α α ℝ)
    (hP_row : ∀ i, (∑ j, P i j) = 1) :
    (∑ j, vecMul v P j) = ∑ i, v i := by
  calc
    (∑ j, vecMul v P j) = ∑ j, ∑ i, v i * P i j := rfl
    _ = ∑ i, v i * (∑ j, P i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ i, v i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hP_row i, mul_one]

omit [DecidableEq α] in
lemma distribution_vecMul
    (v : α → ℝ) (P : Matrix α α ℝ)
    (hv : IsDistribution v)
    (hP_nonneg : ∀ i j, 0 ≤ P i j)
    (hP_row : ∀ i, (∑ j, P i j) = 1) :
    IsDistribution (vecMul v P) := by
  refine ⟨vecMul_nonneg v P hv.1 hP_nonneg, ?_⟩
  calc
    (∑ j, vecMul v P j) = ∑ i, v i := vecMul_sum v P hP_row
    _ = 1 := hv.2

omit [DecidableEq α] in
lemma distribution_vecIter
    (v : α → ℝ) (P : Matrix α α ℝ)
    (hv : IsDistribution v)
    (hP_nonneg : ∀ i j, 0 ≤ P i j)
    (hP_row : ∀ i, (∑ j, P i j) = 1) :
    ∀ n, IsDistribution (vecIter v P n)
  | 0 => hv
  | n + 1 =>
      distribution_vecMul (vecIter v P n) P (distribution_vecIter v P hv hP_nonneg hP_row n)
        hP_nonneg hP_row

omit [DecidableEq α] in
lemma matrixInfNorm_row_le [Nonempty α] (A : Matrix α α ℝ) (i : α) :
    (∑ j, |A i j|) ≤ matrixInfNorm A := by
  classical
  unfold matrixInfNorm
  have hmem : (∑ j, |A i j|) ∈ ((univ : Finset α).image (fun x => ∑ j, |A x j|)) := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  exact Finset.le_max' ((univ : Finset α).image (fun x => ∑ j, |A x j|)) (∑ j, |A i j|) hmem

omit [DecidableEq α] in
lemma matrixInfNorm_nonneg [Nonempty α] (A : Matrix α α ℝ) :
    0 ≤ matrixInfNorm A := by
  rcases (show Nonempty α from inferInstance) with ⟨i⟩
  exact le_trans (Finset.sum_nonneg (fun j hj => abs_nonneg (A i j)))
    (matrixInfNorm_row_le A i)

omit [DecidableEq α] in
lemma matrixInfNorm_le_of_row_bound
    [Nonempty α]
    (A : Matrix α α ℝ)
    (B : ℝ)
    (hrow : ∀ i, (∑ j, |A i j|) ≤ B) :
    matrixInfNorm A ≤ B := by
  classical
  let s : Finset ℝ := (univ : Finset α).image (fun i => ∑ j, |A i j|)
  have hne : s.Nonempty := by
    rcases (show Nonempty α from inferInstance) with ⟨i⟩
    exact ⟨∑ j, |A i j|, by
      change (∑ j, |A i j|) ∈ ((univ : Finset α).image (fun x => ∑ j, |A x j|))
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hmax : s.max' hne ≤ B := by
    refine (Finset.max'_le_iff (s := s) hne).2 ?_
    intro x hx
    have hx' : x ∈ ((univ : Finset α).image (fun i => ∑ j, |A i j|)) := by
      simpa [s] using hx
    rcases Finset.mem_image.mp hx' with ⟨i, hi, rfl⟩
    exact hrow i
  have hs : matrixInfNorm A = s.max' hne := by
    unfold matrixInfNorm
    congr
  calc
    matrixInfNorm A = s.max' hne := hs
    _ ≤ B := hmax

omit [DecidableEq α] in
lemma matrixInfNorm_mul_left_nonneg
    [Nonempty α]
    (c : ℝ) (hc : 0 ≤ c) (A : Matrix α α ℝ) :
    matrixInfNorm (fun i j => c * A i j) = c * matrixInfNorm A := by
  classical
  let sScaled : Finset ℝ := (univ : Finset α).image (fun i => ∑ j, |c * A i j|)
  let sBase : Finset ℝ := (univ : Finset α).image (fun i => ∑ j, |A i j|)
  have hneScaled : sScaled.Nonempty := by
    rcases (show Nonempty α from inferInstance) with ⟨i⟩
    exact ⟨∑ j, |c * A i j|, by
      change (∑ j, |c * A i j|) ∈ ((univ : Finset α).image (fun i => ∑ j, |c * A i j|))
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hleMax : sScaled.max' hneScaled ≤ c * matrixInfNorm A := by
    refine (Finset.max'_le_iff (s := sScaled) hneScaled).2 ?_
    intro x hx
    have hx' : x ∈ ((univ : Finset α).image (fun i => ∑ j, |c * A i j|)) := by
      simpa [sScaled] using hx
    rcases Finset.mem_image.mp hx' with ⟨i, hi, rfl⟩
    calc
      (∑ j, |c * A i j|) = c * (∑ j, |A i j|) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [abs_mul, abs_of_nonneg hc]
      _ ≤ c * matrixInfNorm A := by
        exact mul_le_mul_of_nonneg_left (matrixInfNorm_row_le A i) hc
  have hgeMax : c * matrixInfNorm A ≤ sScaled.max' hneScaled := by
    have hmemBaseMax : matrixInfNorm A ∈ sBase := by
      have htmp : matrixInfNorm A ∈ ((univ : Finset α).image (fun i => ∑ j, |A i j|)) := by
        unfold matrixInfNorm
        exact Finset.max'_mem ((univ : Finset α).image (fun i => ∑ j, |A i j|)) (by
          rcases (show Nonempty α from inferInstance) with ⟨i⟩
          exact ⟨∑ j, |A i j|, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
      simpa [sBase] using htmp
    rcases Finset.mem_image.mp hmemBaseMax with ⟨i, hi, hiEq⟩
    have hmemScaled : (∑ j, |c * A i j|) ∈ sScaled := by
      have hmemScaled' : (∑ j, |c * A i j|) ∈ ((univ : Finset α).image (fun i => ∑ j, |c * A i j|)) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      change (∑ j, |c * A i j|) ∈ ((univ : Finset α).image (fun i => ∑ j, |c * A i j|))
      exact hmemScaled'
    calc
      c * matrixInfNorm A = c * (∑ j, |A i j|) := by rw [hiEq]
      _ = ∑ j, c * |A i j| := by rw [Finset.mul_sum]
      _ = ∑ j, |c * A i j| := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [abs_mul, abs_of_nonneg hc]
      _ ≤ sScaled.max' hneScaled := Finset.le_max' sScaled _ hmemScaled
  have hEqMax : sScaled.max' hneScaled = c * matrixInfNorm A := le_antisymm hleMax hgeMax
  have hScaledDef : matrixInfNorm (fun i j => c * A i j) = sScaled.max' hneScaled := by
    unfold matrixInfNorm
    congr
  calc
    matrixInfNorm (fun i j => c * A i j) = sScaled.max' hneScaled := hScaledDef
    _ = c * matrixInfNorm A := hEqMax

omit [DecidableEq α] in
lemma vecMul_le_matrixInfNorm
    [Nonempty α]
    (v : α → ℝ) (A : Matrix α α ℝ)
    (hv : IsDistribution v) :
    l1Norm (vecMul v A) ≤ matrixInfNorm A := by
  have hpoint :
      ∀ j, |∑ i, v i * A i j| ≤ ∑ i, v i * |A i j| := by
    intro j
    calc
      |∑ i, v i * A i j| ≤ ∑ i, |v i * A i j| := by
        simpa using (abs_sum_le_sum_abs (s := univ) (f := fun i => v i * A i j))
      _ = ∑ i, |v i| * |A i j| := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [abs_mul]
      _ = ∑ i, v i * |A i j| := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [abs_of_nonneg (hv.1 i)]
  calc
    l1Norm (vecMul v A) = ∑ j, |∑ i, v i * A i j| := rfl
    _ ≤ ∑ j, ∑ i, v i * |A i j| := by
      exact Finset.sum_le_sum (fun j hj => hpoint j)
    _ = ∑ i, v i * (∑ j, |A i j|) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
    _ ≤ ∑ i, v i * matrixInfNorm A := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_left (matrixInfNorm_row_le A i) (hv.1 i)
    _ = (∑ i, v i) * matrixInfNorm A := by
      rw [Finset.sum_mul]
    _ = matrixInfNorm A := by
      rw [hv.2, one_mul]

omit [DecidableEq α] in
lemma errorMatrix_row_sum_zero_core
    {P Ptilde : Matrix α α ℝ}
    (hP_row : ∀ i, (∑ j, P i j) = 1)
    (hPtilde_row : ∀ i, (∑ j, Ptilde i j) = 1) :
    ∀ i, (∑ j, errorMatrix P Ptilde i j) = 0 := by
  intro i
  simp [errorMatrix, hP_row i, hPtilde_row i]

/-- Row sums of generator difference `Q - Q̃` are zero. -/
lemma generator_error_row_sum_zero
    (C Ctilde : CTMC α) :
    ∀ i, (∑ j, (C.Q i j - Ctilde.Q i j)) = 0 := by
  intro i
  rw [Finset.sum_sub_distrib, C.row_sum_zero i, Ctilde.row_sum_zero i]
  ring

/-- If each row of `A` sums to `0`, then the row `L1` norm is at most twice the off-diagonal
absolute row sum. -/
lemma row_abs_sum_le_two_mul_offdiag_abs
    (A : Matrix α α ℝ)
    (hrow0 : ∀ i, (∑ j, A i j) = 0) :
    ∀ i, (∑ j, |A i j|) ≤ 2 * (∑ j ∈ (univ.erase i), |A i j|) := by
  intro i
  have hsplitAbs :
      (∑ j, |A i j|) = |A i i| + (∑ j ∈ (univ.erase i), |A i j|) := by
    calc
      (∑ j, |A i j|) = (∑ j ∈ (univ : Finset α).erase i, |A i j|) + |A i i| := by
        exact (Finset.sum_erase_add (s := (univ : Finset α)) (a := i) (f := fun j => |A i j|)
          (Finset.mem_univ i)).symm
      _ = |A i i| + (∑ j ∈ (univ.erase i), |A i j|) := by
        rw [add_comm]
  have hsplit :
      (∑ j, A i j) = A i i + (∑ j ∈ (univ.erase i), A i j) := by
    calc
      (∑ j, A i j) = (∑ j ∈ (univ : Finset α).erase i, A i j) + A i i := by
        exact (Finset.sum_erase_add (s := (univ : Finset α)) (a := i) (f := fun j => A i j)
          (Finset.mem_univ i)).symm
      _ = A i i + (∑ j ∈ (univ.erase i), A i j) := by
        rw [add_comm]
  have hdiag : A i i = -(∑ j ∈ (univ.erase i), A i j) := by
    have hi : (∑ j, A i j) = 0 := hrow0 i
    rw [hsplit] at hi
    linarith
  have hdiagAbs :
      |A i i| ≤ (∑ j ∈ (univ.erase i), |A i j|) := by
    calc
      |A i i| = |∑ j ∈ (univ.erase i), A i j| := by rw [hdiag, abs_neg]
      _ ≤ ∑ j ∈ (univ.erase i), |A i j| := by
        simpa using (abs_sum_le_sum_abs (s := (univ.erase i)) (f := fun j => A i j))
  calc
    (∑ j, |A i j|) = |A i i| + (∑ j ∈ (univ.erase i), |A i j|) := hsplitAbs
    _ ≤ (∑ j ∈ (univ.erase i), |A i j|) + (∑ j ∈ (univ.erase i), |A i j|) := by
      have hleft : |A i i| + (∑ j ∈ (univ.erase i), |A i j|)
          ≤ (∑ j ∈ (univ.erase i), |A i j|) + (∑ j ∈ (univ.erase i), |A i j|) := by
        exact add_le_add hdiagAbs (le_refl _)
      simpa [add_comm, add_left_comm, add_assoc] using hleft
    _ = 2 * (∑ j ∈ (univ.erase i), |A i j|) := by ring

omit [DecidableEq α] in
/-- Markov contraction: row-vector `L1` norm does not increase under a stochastic matrix. -/
theorem markov_contraction_core
    (P : Matrix α α ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j)
    (hP_row : ∀ i, (∑ j, P i j) = 1) :
    ∀ v : α → ℝ, l1Norm (vecMul v P) ≤ l1Norm v := by
  intro v
  have hpoint :
      ∀ j, |∑ i, v i * P i j| ≤ ∑ i, |v i| * P i j := by
    intro j
    calc
      |∑ i, v i * P i j| ≤ ∑ i, |v i * P i j| := by
        simpa using (abs_sum_le_sum_abs (s := univ) (f := fun i => v i * P i j))
      _ = ∑ i, |v i| * P i j := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [abs_mul, abs_of_nonneg (hP_nonneg i j)]
  calc
    l1Norm (vecMul v P) = ∑ j, |∑ i, v i * P i j| := rfl
    _ ≤ ∑ j, ∑ i, |v i| * P i j := by
      exact Finset.sum_le_sum (fun j hj => hpoint j)
    _ = ∑ i, |v i| * (∑ j, P i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ i, |v i| := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hP_row i, mul_one]
    _ = l1Norm v := rfl

omit [DecidableEq α] in
/-- Discrete-time error accumulation bound for two stochastic kernels. -/
theorem nStep_error_bound_core
    [Nonempty α]
    (P Ptilde : Matrix α α ℝ)
    (hP : CTMC.IsStochastic P)
    (hPtilde : CTMC.IsStochastic Ptilde)
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0) :
    ∀ n, l1Norm (fun j => vecIter v0 P n j - vecIter v0 Ptilde n j)
      ≤ (n : ℝ) * matrixInfNorm (errorMatrix P Ptilde) := by
  intro n
  induction' n with n ih
  · simp [vecIter, l1Norm]
  · let a : α → ℝ := vecMul (vecIter v0 P n) P
    let b : α → ℝ := vecMul (vecIter v0 Ptilde n) P
    let c : α → ℝ := vecMul (vecIter v0 Ptilde n) Ptilde
    have hsplit :
        l1Norm (fun j => vecIter v0 P (n + 1) j - vecIter v0 Ptilde (n + 1) j)
          ≤ l1Norm (fun j => a j - b j) + l1Norm (fun j => b j - c j) := by
      have hrew :
          (fun j => vecIter v0 P (n + 1) j - vecIter v0 Ptilde (n + 1) j)
            = (fun j => (a j - b j) + (b j - c j)) := by
        funext j
        simp [a, b, c, vecIter]
      rw [hrew]
      exact l1Norm_add_le (fun j => a j - b j) (fun j => b j - c j)
    have hfirst :
        l1Norm (fun j => a j - b j)
          ≤ l1Norm (fun i => vecIter v0 P n i - vecIter v0 Ptilde n i) := by
      simpa [a, b, vecMul_sub_left] using
        (markov_contraction_core P hP.1 hP.2
          (fun i => vecIter v0 P n i - vecIter v0 Ptilde n i))
    have hdist_tilde :
        IsDistribution (vecIter v0 Ptilde n) := by
      exact distribution_vecIter v0 Ptilde hv0 hPtilde.1 hPtilde.2 n
    have hsecond :
        l1Norm (fun j => b j - c j)
          ≤ matrixInfNorm (errorMatrix P Ptilde) := by
      simpa [b, c, vecMul_sub_right, errorMatrix] using
        (vecMul_le_matrixInfNorm (vecIter v0 Ptilde n) (P - Ptilde) hdist_tilde)
    calc
      l1Norm (fun j => vecIter v0 P (n + 1) j - vecIter v0 Ptilde (n + 1) j)
          ≤ l1Norm (fun j => a j - b j) + l1Norm (fun j => b j - c j) := hsplit
      _ ≤ l1Norm (fun i => vecIter v0 P n i - vecIter v0 Ptilde n i)
          + matrixInfNorm (errorMatrix P Ptilde) := add_le_add hfirst hsecond
      _ ≤ (n : ℝ) * matrixInfNorm (errorMatrix P Ptilde)
          + matrixInfNorm (errorMatrix P Ptilde) := add_le_add ih le_rfl
      _ = ((n : ℝ) + 1) * matrixInfNorm (errorMatrix P Ptilde) := by ring
      _ = ((n + 1 : ℕ) : ℝ) * matrixInfNorm (errorMatrix P Ptilde) := by norm_num

omit [DecidableEq α] in
/-- Infinite weighted version of the `n`-step error estimate. -/
theorem weighted_nStep_error_bound_core
    [Nonempty α]
    (w : ℕ → ℝ)
    (d : ℕ → α → ℝ)
    (B : ℝ)
    (hw_nonneg : ∀ n, 0 ≤ w n)
    (hbound : ∀ n, l1Norm (d n) ≤ (n : ℝ) * B)
    (hwmoment : Summable (fun n => w n * (n : ℝ))) :
    l1Norm (fun i => ∑' n, w n * d n i)
      ≤ (∑' n, w n * (n : ℝ)) * B := by
  have hmomentB : Summable (fun n => w n * ((n : ℝ) * B)) := by
    simpa [mul_assoc] using (hwmoment.mul_right B)
  have hAbsSummable :
      ∀ i, Summable (fun n => |w n * d n i|) := by
    intro i
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_ hmomentB
    intro n
    calc
      |w n * d n i| = w n * |d n i| := by
        rw [abs_mul, abs_of_nonneg (hw_nonneg n)]
      _ ≤ w n * l1Norm (d n) := by
        exact mul_le_mul_of_nonneg_left (abs_le_l1Norm (d n) i) (hw_nonneg n)
      _ ≤ w n * ((n : ℝ) * B) := by
        exact mul_le_mul_of_nonneg_left (hbound n) (hw_nonneg n)
  have hLeft :
      l1Norm (fun i => ∑' n, w n * d n i) ≤ ∑ i, ∑' n, |w n * d n i| := by
    unfold l1Norm
    refine Finset.sum_le_sum ?_
    intro i hi
    have hnorm :
        ‖∑' n, w n * d n i‖ ≤ ∑' n, ‖w n * d n i‖ := by
      exact norm_tsum_le_tsum_norm (hAbsSummable i)
    simpa using hnorm
  have hswap :
      (∑ i, ∑' n, |w n * d n i|) = ∑' n, ∑ i, |w n * d n i| := by
    simpa [Finset.sum_finset_coe] using
      (Summable.tsum_finsetSum (s := (univ : Finset α))
        (f := fun i n => |w n * d n i|)
        (fun i hi => hAbsSummable i)).symm
  have hrow :
      (fun n => ∑ i, |w n * d n i|) = fun n => w n * l1Norm (d n) := by
    funext n
    calc
      (∑ i, |w n * d n i|) = ∑ i, w n * |d n i| := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [abs_mul, abs_of_nonneg (hw_nonneg n)]
      _ = w n * ∑ i, |d n i| := by
        rw [← Finset.mul_sum]
      _ = w n * l1Norm (d n) := rfl
  have hWeightedSummable : Summable (fun n => w n * l1Norm (d n)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hmomentB
    · intro n
      exact mul_nonneg (hw_nonneg n) (l1Norm_nonneg (d n))
    · intro n
      exact mul_le_mul_of_nonneg_left (hbound n) (hw_nonneg n)
  have hWeightedLe :
      (∑' n, w n * l1Norm (d n)) ≤ ∑' n, w n * ((n : ℝ) * B) := by
    exact Summable.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left (hbound n) (hw_nonneg n))
      hWeightedSummable hmomentB
  calc
    l1Norm (fun i => ∑' n, w n * d n i) ≤ ∑ i, ∑' n, |w n * d n i| := hLeft
    _ = ∑' n, ∑ i, |w n * d n i| := hswap
    _ = ∑' n, w n * l1Norm (d n) := by
      exact tsum_congr (fun n => by simpa using congrFun hrow n)
    _ ≤ ∑' n, w n * ((n : ℝ) * B) := hWeightedLe
    _ = (∑' n, w n * (n : ℝ)) * B := by
      simpa [mul_assoc] using (tsum_mul_right (a := B) (f := fun n => w n * (n : ℝ)))

omit [DecidableEq α] in
/-- Continuous-time-style bound from weighted uniformization coefficients. -/
theorem continuous_time_error_bound_with_weights
    [Nonempty α]
    (P Ptilde : Matrix α α ℝ)
    (hP : CTMC.IsStochastic P)
    (hPtilde : CTMC.IsStochastic Ptilde)
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0)
    (w : ℕ → ℝ)
    (hw_nonneg : ∀ n, 0 ≤ w n)
    (hwmoment : Summable (fun n => w n * (n : ℝ))) :
    l1Norm (fun i => ∑' n, w n * (vecIter v0 P n i - vecIter v0 Ptilde n i))
      ≤ (∑' n, w n * (n : ℝ)) * matrixInfNorm (errorMatrix P Ptilde) := by
  apply weighted_nStep_error_bound_core
    (w := w)
    (d := fun n i => vecIter v0 P n i - vecIter v0 Ptilde n i)
    (B := matrixInfNorm (errorMatrix P Ptilde))
  · exact hw_nonneg
  · intro n
    exact nStep_error_bound_core P Ptilde hP hPtilde v0 hv0 n
  · exact hwmoment

lemma shifted_term_eq (r : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * r ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)
      = r * (r ^ n / (Nat.factorial n : ℝ)) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

lemma hasSum_nat_mul_pow_div_factorial (r : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * r ^ n / (Nat.factorial n : ℝ)) (r * Real.exp r) := by
  let f : ℕ → ℝ := fun n => (n : ℝ) * r ^ n / (Nat.factorial n : ℝ)
  have hExp : HasSum (fun n : ℕ => r ^ n / (Nat.factorial n : ℝ)) (Real.exp r) := by
    simpa [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp r)
  have hScaled : HasSum (fun n : ℕ => r * (r ^ n / (Nat.factorial n : ℝ))) (r * Real.exp r) :=
    hExp.mul_left r
  have hShift : HasSum (fun n : ℕ => f (n + 1)) (r * Real.exp r) := by
    convert hScaled using 1
    ext n
    simp [f]
    exact shifted_term_eq r n
  have hs : Summable f := by
    exact (summable_nat_add_iff 1).1 hShift.summable
  have hsum : (∑ i ∈ Finset.range 1, f i) + (∑' i : ℕ, f (i + 1)) = ∑' i : ℕ, f i :=
    hs.sum_add_tsum_nat_add 1
  have h0 : ∑ i ∈ Finset.range 1, f i = 0 := by
    simp [f]
  have htsum : (∑' i : ℕ, f i) = r * Real.exp r := by
    calc
      (∑' i : ℕ, f i) = (∑ i ∈ Finset.range 1, f i) + (∑' i : ℕ, f (i + 1)) := by
        simpa [add_comm] using hsum.symm
      _ = 0 + (r * Real.exp r) := by rw [h0, hShift.tsum_eq]
      _ = r * Real.exp r := by ring
  exact (hs.hasSum_iff).2 htsum

theorem poissonPMFReal_firstMoment_hasSum (r : NNReal) :
    HasSum (fun n : ℕ => (n : ℝ) * ProbabilityTheory.poissonPMFReal r n) (r : ℝ) := by
  have hMom : HasSum (fun n : ℕ => (n : ℝ) * (r : ℝ) ^ n / (Nat.factorial n : ℝ))
      ((r : ℝ) * Real.exp (r : ℝ)) :=
    hasSum_nat_mul_pow_div_factorial (r : ℝ)
  have hScaled : HasSum
      (fun n : ℕ => Real.exp (-(r : ℝ)) * ((n : ℝ) * (r : ℝ) ^ n / (Nat.factorial n : ℝ)))
      (Real.exp (-(r : ℝ)) * ((r : ℝ) * Real.exp (r : ℝ))) := by
    exact hMom.mul_left (Real.exp (-(r : ℝ)))
  have hEqFn :
      (fun n : ℕ => (n : ℝ) * ProbabilityTheory.poissonPMFReal r n)
      = (fun n : ℕ => Real.exp (-(r : ℝ)) * ((n : ℝ) * (r : ℝ) ^ n / (Nat.factorial n : ℝ))) := by
    funext n
    simp [ProbabilityTheory.poissonPMFReal]
    ring
  rw [hEqFn]
  convert hScaled using 1
  symm
  calc
    Real.exp (-(r : ℝ)) * ((r : ℝ) * Real.exp (r : ℝ))
        = (Real.exp (r : ℝ))⁻¹ * ((r : ℝ) * Real.exp (r : ℝ)) := by
          rw [Real.exp_neg]
    _ = ((Real.exp (r : ℝ))⁻¹ * Real.exp (r : ℝ)) * (r : ℝ) := by ring
    _ = (1 : ℝ) * (r : ℝ) := by
          rw [inv_mul_cancel₀ (Real.exp_ne_zero (r : ℝ))]
    _ = (r : ℝ) := by ring

theorem poissonPMFReal_firstMoment_tsum_core (r : NNReal) :
    (∑' n : ℕ, ProbabilityTheory.poissonPMFReal r n * (n : ℝ)) = (r : ℝ) := by
  have hHas : HasSum (fun n : ℕ => ProbabilityTheory.poissonPMFReal r n * (n : ℝ)) (r : ℝ) := by
    convert (poissonPMFReal_firstMoment_hasSum r) using 1
    ext n
    ring
  exact hHas.tsum_eq

omit [DecidableEq α] in
theorem continuous_time_error_bound_poisson_core
    [Nonempty α]
    (P Ptilde : Matrix α α ℝ)
    (hP : CTMC.IsStochastic P)
    (hPtilde : CTMC.IsStochastic Ptilde)
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0)
    (r : NNReal) :
    l1Norm (fun i => ∑' n, ProbabilityTheory.poissonPMFReal r n
      * (vecIter v0 P n i - vecIter v0 Ptilde n i))
      ≤ (r : ℝ) * matrixInfNorm (errorMatrix P Ptilde) := by
  have hMomentSummable :
      Summable (fun n : ℕ => ProbabilityTheory.poissonPMFReal r n * (n : ℝ)) := by
    have hMomentSummable' :
        Summable (fun n : ℕ => (n : ℝ) * ProbabilityTheory.poissonPMFReal r n) := by
      exact (poissonPMFReal_firstMoment_hasSum r).summable
    convert hMomentSummable' using 1
    ext n
    ring
  have hWeighted :=
    continuous_time_error_bound_with_weights
      (P := P) (Ptilde := Ptilde) hP hPtilde (v0 := v0) hv0
      (w := ProbabilityTheory.poissonPMFReal r)
      (hw_nonneg := fun n => ProbabilityTheory.poissonPMFReal_nonneg (r := r) (n := n))
      (hwmoment := hMomentSummable)
  simpa [poissonPMFReal_firstMoment_tsum_core (r := r)] using hWeighted

omit [DecidableEq α] in
/-- Main continuous-time form with scaled generator error term `ΔQ = γ * ΔP`. -/
theorem continuous_time_error_bound_main_uniformized
    [Nonempty α]
    (P Ptilde : Matrix α α ℝ)
    (hP : CTMC.IsStochastic P)
    (hPtilde : CTMC.IsStochastic Ptilde)
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0)
    (γ t : NNReal) :
    l1Norm (fun i => ∑' n, ProbabilityTheory.poissonPMFReal (γ * t) n
      * (vecIter v0 P n i - vecIter v0 Ptilde n i))
      ≤ (t : ℝ) * matrixInfNorm (fun i j => (γ : ℝ) * errorMatrix P Ptilde i j) := by
  have hbase := continuous_time_error_bound_poisson_core
    (P := P) (Ptilde := Ptilde) hP hPtilde (v0 := v0) hv0 (r := γ * t)
  have hscale :
      matrixInfNorm (fun i j => (γ : ℝ) * errorMatrix P Ptilde i j)
        = (γ : ℝ) * matrixInfNorm (errorMatrix P Ptilde) := by
    simpa using matrixInfNorm_mul_left_nonneg (c := (γ : ℝ)) (hc := by exact_mod_cast γ.2)
      (A := errorMatrix P Ptilde)
  calc
    l1Norm (fun i => ∑' n, ProbabilityTheory.poissonPMFReal (γ * t) n
      * (vecIter v0 P n i - vecIter v0 Ptilde n i))
        ≤ ((γ * t : NNReal) : ℝ) * matrixInfNorm (errorMatrix P Ptilde) := hbase
    _ = (t : ℝ) * ((γ : ℝ) * matrixInfNorm (errorMatrix P Ptilde)) := by
      rw [NNReal.coe_mul]
      ring
    _ = (t : ℝ) * matrixInfNorm (fun i j => (γ : ℝ) * errorMatrix P Ptilde i j) := by
      rw [hscale]

lemma uniformized_error_scaled_eq_generator_error
    (C Ctilde : CTMC α)
    {γ : ℝ}
    (hγpos : 0 < γ) :
    (fun i j => γ * errorMatrix (C.uniformized γ) (Ctilde.uniformized γ) i j)
      = (fun i j => C.Q i j - Ctilde.Q i j) := by
  have hγnz : γ ≠ 0 := by linarith
  funext i j
  by_cases hij : i = j
  · subst hij
    simp [errorMatrix, CTMC.uniformized, C.diag_eq_neg_exitRate, Ctilde.diag_eq_neg_exitRate]
    field_simp [hγnz]
    ring
  · simp [errorMatrix, CTMC.uniformized, hij]
    field_simp [hγnz]

/-- Generator-level continuous-time error bound for uniformization with common rate `γ`. -/
theorem continuous_time_error_bound_generators_core
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
      ≤ (t : ℝ) * matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) := by
  have hP : CTMC.IsStochastic (C.uniformized (γ : ℝ)) :=
    C.uniformized_isStochastic hγpos hγbound
  have hPtilde : CTMC.IsStochastic (Ctilde.uniformized (γ : ℝ)) :=
    Ctilde.uniformized_isStochastic hγpos hγbound_tilde
  have hmain :=
    continuous_time_error_bound_main_uniformized
      (P := C.uniformized (γ : ℝ)) (Ptilde := Ctilde.uniformized (γ : ℝ))
      hP hPtilde (v0 := v0) hv0 (γ := γ) (t := t)
  have hDelta :
      (fun i j => (γ : ℝ) * errorMatrix (C.uniformized (γ : ℝ)) (Ctilde.uniformized (γ : ℝ)) i j)
        = (fun i j => C.Q i j - Ctilde.Q i j) := by
    simpa using
      (uniformized_error_scaled_eq_generator_error (C := C) (Ctilde := Ctilde)
        (γ := (γ : ℝ)) hγpos)
  simpa [hDelta] using hmain

/-- Reachability-style corollary: projection to any target set is bounded by the `L1` error. -/
theorem reachability_error_bound_generators_core
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
    |∑ i ∈ F, diff i| ≤ (t : ℝ) * matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) := by
  intro diff
  have hmain :
      l1Norm diff ≤ (t : ℝ) * matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) := by
    simpa [diff] using
      (continuous_time_error_bound_generators_core
        (C := C) (Ctilde := Ctilde) (γ := γ) (t := t) hγpos hγbound hγbound_tilde
        (v0 := v0) hv0)
  have hproj : |∑ i ∈ F, diff i| ≤ l1Norm diff := by
    calc
      |∑ i ∈ F, diff i| ≤ ∑ i ∈ F, |diff i| := by
        simpa using (abs_sum_le_sum_abs (s := F) (f := fun i => diff i))
      _ ≤ ∑ i, |diff i| := by
        exact Finset.sum_le_univ_sum_of_nonneg (s := F) (w := fun i => abs_nonneg (diff i))
      _ = l1Norm diff := rfl
  exact le_trans hproj hmain

/-- Blockwise variation budget `max_k Σ_{ℓ≠k} term(k,ℓ)`. -/
noncomputable def blockVariationBudget
    [Fintype β] [DecidableEq β] [Nonempty β]
    (term : β → β → ℝ) : ℝ :=
  ((univ : Finset β).image (fun k => ∑ ℓ ∈ (univ.erase k), term k ℓ)).max' (by
    rcases (show Nonempty β from inferInstance) with ⟨k⟩
    exact ⟨∑ ℓ ∈ (univ.erase k), term k ℓ, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩)

lemma blockSum_le_blockVariationBudget
    [Fintype β] [DecidableEq β] [Nonempty β]
    (term : β → β → ℝ)
    (k : β) :
    (∑ ℓ ∈ (univ.erase k), term k ℓ) ≤ blockVariationBudget term := by
  classical
  unfold blockVariationBudget
  have hmem :
      (∑ ℓ ∈ (univ.erase k), term k ℓ) ∈
        ((univ : Finset β).image (fun x => ∑ ℓ ∈ (univ.erase x), term x ℓ)) := by
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  exact Finset.le_max' ((univ : Finset β).image (fun x => ∑ ℓ ∈ (univ.erase x), term x ℓ))
    (∑ ℓ ∈ (univ.erase k), term k ℓ) hmem

/-- If each concrete row is bounded by a blockwise sum, then `‖ΔQ‖∞` is bounded by the
corresponding blockwise maximum. -/
theorem generator_error_norm_le_two_mul_blockVariationBudget
    [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (C Ctilde : CTMC α)
    (αmap : α → β)
    (term : β → β → ℝ)
    (hrow :
      ∀ i, (∑ j, |C.Q i j - Ctilde.Q i j|) ≤
        2 * (∑ ℓ ∈ (univ.erase (αmap i)), term (αmap i) ℓ)) :
    matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) ≤ 2 * blockVariationBudget term := by
  have hrow' :
      ∀ i, (∑ j, |(fun i j => C.Q i j - Ctilde.Q i j) i j|) ≤ 2 * blockVariationBudget term := by
    intro i
    calc
      (∑ j, |(fun i j => C.Q i j - Ctilde.Q i j) i j|)
          = (∑ j, |C.Q i j - Ctilde.Q i j|) := by simp
      _ ≤ 2 * (∑ ℓ ∈ (univ.erase (αmap i)), term (αmap i) ℓ) := hrow i
      _ ≤ 2 * blockVariationBudget term := by
        exact mul_le_mul_of_nonneg_left
          (blockSum_le_blockVariationBudget (term := term) (k := αmap i)) (by norm_num)
  simpa using
    (matrixInfNorm_le_of_row_bound
      (A := fun i j => C.Q i j - Ctilde.Q i j)
      (B := 2 * blockVariationBudget term)
      hrow')

/-- Explicit reachability bound from a blockwise row bound on generator error. -/
theorem explicit_reachability_error_bound_from_block_row_bound
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
    (term : β → β → ℝ)
    (hrow :
      ∀ i, (∑ j, |C.Q i j - Ctilde.Q i j|) ≤
        2 * (∑ ℓ ∈ (univ.erase (αmap i)), term (αmap i) ℓ)) :
    let diff : α → ℝ :=
      fun i => ∑' n, ProbabilityTheory.poissonPMFReal (γ * t) n
        * (vecIter v0 (C.uniformized (γ : ℝ)) n i - vecIter v0 (Ctilde.uniformized (γ : ℝ)) n i)
    |∑ i ∈ F, diff i| ≤ 2 * (t : ℝ) * blockVariationBudget term := by
  intro diff
  have hDeltaQ :
      matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) ≤ 2 * blockVariationBudget term := by
    exact generator_error_norm_le_two_mul_blockVariationBudget
      (C := C) (Ctilde := Ctilde) (αmap := αmap) (term := term) hrow
  have hreach :
      |∑ i ∈ F, diff i| ≤ (t : ℝ) * matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) := by
    simpa [diff] using
      (reachability_error_bound_generators_core
        (C := C) (Ctilde := Ctilde) (γ := γ) (t := t) hγpos hγbound hγbound_tilde
        (v0 := v0) hv0 (F := F))
  have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast t.2
  calc
    |∑ i ∈ F, diff i| ≤ (t : ℝ) * matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) := hreach
    _ ≤ (t : ℝ) * (2 * blockVariationBudget term) := mul_le_mul_of_nonneg_left hDeltaQ ht_nonneg
    _ = 2 * (t : ℝ) * blockVariationBudget term := by ring

/-- Explicit reachability bound from a deviation bound plus a row-decomposition inequality. -/
theorem explicit_reachability_error_bound_from_deviation
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
    (term : β → β → ℝ)
    (hrowSplit :
      ∀ i, (∑ j, |C.Q i j - Ctilde.Q i j|) ≤
        2 * (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|))
    (hdev :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        |r i ℓ - rHat (αmap i) ℓ| ≤ term (αmap i) ℓ) :
    let diff : α → ℝ :=
      fun i => ∑' n, ProbabilityTheory.poissonPMFReal (γ * t) n
        * (vecIter v0 (C.uniformized (γ : ℝ)) n i - vecIter v0 (Ctilde.uniformized (γ : ℝ)) n i)
    |∑ i ∈ F, diff i| ≤ 2 * (t : ℝ) * blockVariationBudget term := by
  intro diff
  have hrow :
      ∀ i, (∑ j, |C.Q i j - Ctilde.Q i j|) ≤
        2 * (∑ ℓ ∈ (univ.erase (αmap i)), term (αmap i) ℓ) := by
    intro i
    have hsum :
        (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|) ≤
          (∑ ℓ ∈ (univ.erase (αmap i)), term (αmap i) ℓ) := by
      exact Finset.sum_le_sum (by intro ℓ hℓ; exact hdev i ℓ hℓ)
    calc
      (∑ j, |C.Q i j - Ctilde.Q i j|) ≤
          2 * (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|) := hrowSplit i
      _ ≤ 2 * (∑ ℓ ∈ (univ.erase (αmap i)), term (αmap i) ℓ) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  exact explicit_reachability_error_bound_from_block_row_bound
    (C := C) (Ctilde := Ctilde) (γ := γ) (t := t)
    hγpos hγbound hγbound_tilde (v0 := v0) hv0 (F := F)
    (αmap := αmap) (term := term) hrow

/-- Off-diagonal absolute row sums are controlled by blockwise absolute aggregate differences,
under intra-block cancellation and per-block sign coherence assumptions. -/
lemma offdiag_abs_le_block_abs_of_sign_coherent
    [Fintype β] [DecidableEq β]
    (αmap : α → β)
    (A : Matrix α α ℝ)
    (r : α → β → ℝ)
    (rHat : β → β → ℝ)
    (hIntraZero : ∀ i j, j ≠ i → αmap j = αmap i → A i j = 0)
    (hSign :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        (∀ j, αmap j = ℓ → 0 ≤ A i j) ∨ (∀ j, αmap j = ℓ → A i j ≤ 0))
    (hBlockSum :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        (∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j) = r i ℓ - rHat (αmap i) ℓ) :
    ∀ i, (∑ j ∈ (univ.erase i), |A i j|) ≤
      (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|) := by
  intro i
  have hFilterEq :
      (∑ j ∈ (univ.erase i), |A i j|) =
        (∑ j ∈ (univ.erase i) with αmap j ∈ (univ.erase (αmap i)), |A i j|) := by
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not (s := (univ.erase i))
        (p := fun j => αmap j ∈ (univ.erase (αmap i))) (f := fun j => |A i j|)
    have hzero :
        (∑ j ∈ (univ.erase i) with ¬ (αmap j ∈ (univ.erase (αmap i))), |A i j|) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hjm : j ∈ (univ.erase i) := (Finset.mem_filter.mp hj).1
      have hjne : j ≠ i := (Finset.mem_erase.mp hjm).1
      have hnot : ¬ αmap j ∈ (univ.erase (αmap i)) := (Finset.mem_filter.mp hj).2
      have hEq : αmap j = αmap i := by
        by_contra hNe
        exact hnot (Finset.mem_erase.mpr ⟨hNe, Finset.mem_univ _⟩)
      have hA0 : A i j = 0 := hIntraZero i j hjne hEq
      simp [hA0]
    linarith [hsplit, hzero]
  have hFiber :
      (∑ j ∈ (univ.erase i) with αmap j ∈ (univ.erase (αmap i)), |A i j|) =
        (∑ ℓ ∈ (univ.erase (αmap i)), ∑ j ∈ (univ.erase i) with αmap j = ℓ, |A i j|) := by
    simpa using
      (Finset.sum_fiberwise_eq_sum_filter
        (s := (univ.erase i)) (t := (univ.erase (αmap i)))
        (g := αmap) (f := fun j => |A i j|)).symm
  have hInner :
      ∀ ℓ, ℓ ∈ (univ.erase (αmap i)) →
        (∑ j ∈ (univ.erase i) with αmap j = ℓ, |A i j|) = |r i ℓ - rHat (αmap i) ℓ| := by
    intro ℓ hℓ
    rcases hSign i ℓ hℓ with hNonneg | hNonpos
    · have habs :
          (∑ j ∈ (univ.erase i) with αmap j = ℓ, |A i j|) =
            (∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact abs_of_nonneg (hNonneg j (Finset.mem_filter.mp hj).2)
      have hsumNonneg :
          0 ≤ (∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j) := by
        exact Finset.sum_nonneg (by
          intro j hj
          exact hNonneg j (Finset.mem_filter.mp hj).2)
      calc
        (∑ j ∈ (univ.erase i) with αmap j = ℓ, |A i j|)
            = (∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j) := habs
        _ = |∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j| := by
          rw [abs_of_nonneg hsumNonneg]
        _ = |r i ℓ - rHat (αmap i) ℓ| := by rw [hBlockSum i ℓ hℓ]
    · have habs :
          (∑ j ∈ (univ.erase i) with αmap j = ℓ, |A i j|) =
            - (∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j) := by
        calc
          (∑ j ∈ (univ.erase i) with αmap j = ℓ, |A i j|)
              = (∑ j ∈ (univ.erase i) with αmap j = ℓ, -A i j) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                exact abs_of_nonpos (hNonpos j (Finset.mem_filter.mp hj).2)
          _ = - (∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j) := by
                rw [← Finset.sum_neg_distrib]
      have hsumNonpos :
          (∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j) ≤ 0 := by
        exact Finset.sum_nonpos (by
          intro j hj
          exact hNonpos j (Finset.mem_filter.mp hj).2)
      calc
        (∑ j ∈ (univ.erase i) with αmap j = ℓ, |A i j|)
            = - (∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j) := habs
        _ = |∑ j ∈ (univ.erase i) with αmap j = ℓ, A i j| := by
          rw [abs_of_nonpos hsumNonpos]
        _ = |r i ℓ - rHat (αmap i) ℓ| := by rw [hBlockSum i ℓ hℓ]
  calc
    (∑ j ∈ (univ.erase i), |A i j|)
        = (∑ j ∈ (univ.erase i) with αmap j ∈ (univ.erase (αmap i)), |A i j|) := hFilterEq
    _ = (∑ ℓ ∈ (univ.erase (αmap i)), ∑ j ∈ (univ.erase i) with αmap j = ℓ, |A i j|) := hFiber
    _ = (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|) := by
      refine Finset.sum_congr rfl ?_
      intro ℓ hℓ
      exact hInner ℓ hℓ
    _ ≤ (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|) := le_rfl

/-- Explicit reachability bound from off-diagonal aggregation plus a deviation bound. -/
theorem explicit_reachability_error_bound_from_offdiag_deviation
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
    (term : β → β → ℝ)
    (hoffDiag :
      ∀ i, (∑ j ∈ (univ.erase i), |C.Q i j - Ctilde.Q i j|) ≤
        (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|))
    (hdev :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        |r i ℓ - rHat (αmap i) ℓ| ≤ term (αmap i) ℓ) :
    let diff : α → ℝ :=
      fun i => ∑' n, ProbabilityTheory.poissonPMFReal (γ * t) n
        * (vecIter v0 (C.uniformized (γ : ℝ)) n i - vecIter v0 (Ctilde.uniformized (γ : ℝ)) n i)
    |∑ i ∈ F, diff i| ≤ 2 * (t : ℝ) * blockVariationBudget term := by
  intro diff
  have hrowSplit :
      ∀ i, (∑ j, |C.Q i j - Ctilde.Q i j|) ≤
        2 * (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|) := by
    intro i
    have hrow0 :
        ∀ x, (∑ j, ((fun a b => C.Q a b - Ctilde.Q a b) x j)) = 0 := by
      intro x
      simpa using (generator_error_row_sum_zero (C := C) (Ctilde := Ctilde) x)
    have htwo :
        (∑ j, |C.Q i j - Ctilde.Q i j|) ≤ 2 * (∑ j ∈ (univ.erase i), |C.Q i j - Ctilde.Q i j|) := by
      simpa using
        (row_abs_sum_le_two_mul_offdiag_abs
          (A := fun a b => C.Q a b - Ctilde.Q a b) hrow0 i)
    calc
      (∑ j, |C.Q i j - Ctilde.Q i j|) ≤ 2 * (∑ j ∈ (univ.erase i), |C.Q i j - Ctilde.Q i j|) := htwo
      _ ≤ 2 * (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|) := by
        exact mul_le_mul_of_nonneg_left (hoffDiag i) (by norm_num)
  exact explicit_reachability_error_bound_from_deviation
    (C := C) (Ctilde := Ctilde) (γ := γ) (t := t)
    hγpos hγbound hγbound_tilde (v0 := v0) hv0 (F := F)
    (αmap := αmap) (r := r) (rHat := rHat) (term := term)
    hrowSplit hdev

/-- Variation-ratio specialization of the explicit bound. -/
theorem explicit_reachability_error_bound_from_variation_ratio
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
    (hrowSplit :
      ∀ i, (∑ j, |C.Q i j - Ctilde.Q i j|) ≤
        2 * (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|))
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
    |∑ i ∈ F, diff i| ≤ 2 * (t : ℝ) * blockVariationBudget term := by
  intro term diff
  have hdev :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        |r i ℓ - rHat (αmap i) ℓ| ≤ term (αmap i) ℓ := by
    intro i ℓ hℓ
    rcases hrBounds i ℓ hℓ with ⟨hri_lo, hri_hi⟩
    rcases hrHatBounds i ℓ hℓ with ⟨hrh_lo, hrh_hi⟩
    have htmp :=
      PredicateAbstraction.PaperProofs.deviationBoundFromVariationRatio_core
        (x := r i ℓ) (xhat := rHat (αmap i) ℓ)
        (rmin := rmin (αmap i) ℓ) (rmax := rmax (αmap i) ℓ) (V := V (αmap i) ℓ)
        hri_lo hri_hi hrh_lo hrh_hi (hrminPos i ℓ hℓ) (hVdef (αmap i) ℓ)
    simpa [term] using htmp
  exact explicit_reachability_error_bound_from_deviation
    (C := C) (Ctilde := Ctilde) (γ := γ) (t := t)
    hγpos hγbound hγbound_tilde (v0 := v0) hv0 (F := F)
    (αmap := αmap) (r := r) (rHat := rHat) (term := term)
    hrowSplit hdev

/-- Variation-ratio explicit bound with off-diagonal aggregation derived from structural
block assumptions (intra-block cancellation, sign coherence, block-sum identity). -/
theorem explicit_reachability_error_bound_from_variation_ratio_sign_coherent_core
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
    |∑ i ∈ F, diff i| ≤ 2 * (t : ℝ) * blockVariationBudget term := by
  intro term diff
  have hoffDiag :
      ∀ i, (∑ j ∈ (univ.erase i), |C.Q i j - Ctilde.Q i j|) ≤
        (∑ ℓ ∈ (univ.erase (αmap i)), |r i ℓ - rHat (αmap i) ℓ|) := by
    exact offdiag_abs_le_block_abs_of_sign_coherent
      (αmap := αmap) (A := fun i j => C.Q i j - Ctilde.Q i j)
      (r := r) (rHat := rHat) hIntraZero hSign hBlockSum
  have hdev :
      ∀ i ℓ, ℓ ∈ (univ.erase (αmap i)) →
        |r i ℓ - rHat (αmap i) ℓ| ≤ term (αmap i) ℓ := by
    intro i ℓ hℓ
    rcases hrBounds i ℓ hℓ with ⟨hri_lo, hri_hi⟩
    rcases hrHatBounds i ℓ hℓ with ⟨hrh_lo, hrh_hi⟩
    have htmp :=
      PredicateAbstraction.PaperProofs.deviationBoundFromVariationRatio_core
        (x := r i ℓ) (xhat := rHat (αmap i) ℓ)
        (rmin := rmin (αmap i) ℓ) (rmax := rmax (αmap i) ℓ) (V := V (αmap i) ℓ)
        hri_lo hri_hi hrh_lo hrh_hi (hrminPos i ℓ hℓ) (hVdef (αmap i) ℓ)
    simpa [term] using htmp
  exact explicit_reachability_error_bound_from_offdiag_deviation
    (C := C) (Ctilde := Ctilde) (γ := γ) (t := t)
    hγpos hγbound hγbound_tilde (v0 := v0) hv0 (F := F)
    (αmap := αmap) (r := r) (rHat := rHat) (term := term)
    hoffDiag hdev

/-- Explicit-form reachability bound, assuming an explicit upper bound on `‖ΔQ‖∞`. -/
theorem explicit_reachability_error_bound_generators
    [Nonempty α]
    (C Ctilde : CTMC α)
    (γ t : NNReal)
    (hγpos : 0 < (γ : ℝ))
    (hγbound : ∀ i, C.exitRate i ≤ (γ : ℝ))
    (hγbound_tilde : ∀ i, Ctilde.exitRate i ≤ (γ : ℝ))
    (v0 : α → ℝ)
    (hv0 : IsDistribution v0)
    (F : Finset α)
    (B : ℝ)
    (hDeltaQ : matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) ≤ 2 * B) :
    let diff : α → ℝ :=
      fun i => ∑' n, ProbabilityTheory.poissonPMFReal (γ * t) n
        * (vecIter v0 (C.uniformized (γ : ℝ)) n i - vecIter v0 (Ctilde.uniformized (γ : ℝ)) n i)
    |∑ i ∈ F, diff i| ≤ 2 * (t : ℝ) * B := by
  intro diff
  have hreach :
      |∑ i ∈ F, diff i| ≤ (t : ℝ) * matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) := by
    simpa [diff] using
      (reachability_error_bound_generators_core
        (C := C) (Ctilde := Ctilde) (γ := γ) (t := t) hγpos hγbound hγbound_tilde
        (v0 := v0) hv0 (F := F))
  have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast t.2
  calc
    |∑ i ∈ F, diff i| ≤ (t : ℝ) * matrixInfNorm (fun i j => C.Q i j - Ctilde.Q i j) := hreach
    _ ≤ (t : ℝ) * (2 * B) := mul_le_mul_of_nonneg_left hDeltaQ ht_nonneg
    _ = 2 * (t : ℝ) * B := by ring

end ErrorAndContraction

end FiniteState

end CTMCFormalization
end PredicateAbstraction
