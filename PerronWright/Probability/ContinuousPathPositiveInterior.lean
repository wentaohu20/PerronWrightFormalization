import PerronWright.Probability.ContinuousPathIntervalMinimum

/-! # Strict positivity on a compact interval interior is a Borel event

Strict positivity is tested by attained minima on countably many rational
compact subintervals, not by positivity at rational sample points alone.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ContinuousPathPositiveInterior

open BrownianPathLaw ContinuousPathIntervalMinimum

def positiveInterior (T : ℝ≥0) : Set Path := {f | ∀ t : ℝ≥0, 0 < t → t < T → 0 < f t}

theorem positiveInterior_iff_rational_interval_minima (T : ℝ≥0) (f : Path) :
    f ∈ positiveInterior T ↔ ∀ q r : ℚ,
      0 < Real.toNNReal (q : ℝ) → Real.toNNReal (q : ℝ) ≤ Real.toNNReal (r : ℝ) →
      Real.toNNReal (r : ℝ) < T →
      0 < intervalMinimum (Real.toNNReal (q : ℝ)) (Real.toNNReal (r : ℝ)) f := by
  constructor
  · intro hf q r hq hqr hr
    obtain ⟨t,ht,he,_⟩ := exists_intervalMinimum _ _ hqr f
    rw [he]
    exact hf t (hq.trans_le ht.1) (ht.2.trans_lt hr)
  · intro hf t ht htT
    obtain ⟨q,hq0,hqt⟩ := exists_rat_btwn (show 0 < (t : ℝ) from ht)
    obtain ⟨r,htr,hrT⟩ := exists_rat_btwn (show (t : ℝ) < T from htT)
    have hq : 0 < Real.toNNReal (q : ℝ) := Real.toNNReal_pos.mpr hq0
    have hqt' : Real.toNNReal (q : ℝ) ≤ t := Real.toNNReal_le_iff_le_coe.mpr hqt.le
    have htr' : t ≤ Real.toNNReal (r : ℝ) :=
      (Real.le_toNNReal_iff_coe_le (t.coe_nonneg.trans htr.le)).mpr htr.le
    have hr : Real.toNNReal (r : ℝ) < T :=
      (Real.toNNReal_lt_iff_lt_coe (t.coe_nonneg.trans htr.le)).mpr hrT
    have hqr := hqt'.trans htr'
    exact (hf q r hq hqr hr).trans_le (intervalMinimum_le _ _ hqr f t ⟨hqt',htr'⟩)

theorem measurableSet_positiveInterior (T : ℝ≥0) : MeasurableSet (positiveInterior T) := by
  have he : positiveInterior T = ⋂ q : ℚ, ⋂ r : ℚ, {f : Path |
      0 < Real.toNNReal (q : ℝ) → Real.toNNReal (q : ℝ) ≤ Real.toNNReal (r : ℝ) →
      Real.toNNReal (r : ℝ) < T →
      0 < intervalMinimum (Real.toNNReal (q : ℝ)) (Real.toNNReal (r : ℝ)) f} := by
    ext f
    simp only [mem_iInter,mem_ofPred_eq]
    exact positiveInterior_iff_rational_interval_minima T f
  rw [he]
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.iInter
  intro r
  by_cases hq : 0 < Real.toNNReal (q : ℝ)
  · by_cases hqr : Real.toNNReal (q : ℝ) ≤ Real.toNNReal (r : ℝ)
    · by_cases hr : Real.toNNReal (r : ℝ) < T
      · simpa only [hq,hqr,hr,true_implies] using
          (measurableSet_lt measurable_const (continuous_intervalMinimum _ _).measurable)
      · simp only [hr,false_implies,implies_true,Set.ofPred_true]
        exact MeasurableSet.univ
    · simp only [hqr,false_implies,implies_true,Set.ofPred_true]
      exact MeasurableSet.univ
  · simp only [hq,false_implies,Set.ofPred_true]
    exact MeasurableSet.univ

end PerronWright.ContinuousPathPositiveInterior
