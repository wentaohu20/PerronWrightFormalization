import PerronWright.Probability.BrownianReflectedAreaCounts

/-!
# Literal planar Lebesgue intensity under actual reflected Brownian paths

For each bounded real-time interval, the region under the genuine reflected
path is measurable and has finite planar Lebesgue mass exactly equal to its
proved area rate. This identifies the rates with unit planar intensity;
it does not postulate or construct a spatial Poisson point process.
-/

open MeasureTheory
open scoped Classical NNReal ENNReal

noncomputable section

namespace PerronWright.BrownianUnderGraphIntensity

open BrownianPathLaw BrownianReflectedAreaCounts

def region (lambda : ℝ) (a b : ℝ≥0) (f : Path) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (a : ℝ) (b : ℝ) ∧ 0 < p.2 ∧ p.2 < surface lambda f p.1}

theorem measurableSet_region (lambda : ℝ) (a b : ℝ≥0) (f : Path) :
    MeasurableSet (region lambda a b f) := by
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd ((continuous_surface lambda f).measurable.comp measurable_fst)))

theorem vertical_section (lambda : ℝ) (a b : ℝ≥0) (f : Path) (s : ℝ) :
    Prod.mk s ⁻¹' region lambda a b f =
      if s ∈ Set.Icc (a : ℝ) (b : ℝ) then Set.Ioo 0 (surface lambda f s) else ∅ := by
  ext y
  change (s ∈ Set.Icc (a : ℝ) (b : ℝ) ∧ 0 < y ∧ y < surface lambda f s) ↔ _
  by_cases hs : s ∈ Set.Icc (a : ℝ) (b : ℝ)
  · simp only [hs,if_true,Set.mem_Ioo,true_and]
  · simp only [hs,if_false,Set.mem_empty_iff_false,false_and]

/-- The rate is exactly the unit planar intensity of the bounded region. -/
theorem volume_region (lambda : ℝ) (a b : ℝ≥0) (f : Path) :
    volume (region lambda a b f) = ENNReal.ofReal (realArea lambda a b f) := by
  rw [Measure.volume_eq_prod,Measure.prod_apply (measurableSet_region lambda a b f)]
  simp only [vertical_section]
  have hslice : (fun s : ℝ ↦ volume
      (if s ∈ Set.Icc (a : ℝ) (b : ℝ) then Set.Ioo 0 (surface lambda f s) else ∅)) =
      (Set.Icc (a : ℝ) (b : ℝ)).indicator
        (fun s ↦ ENNReal.ofReal (surface lambda f s)) := by
    funext s
    by_cases hs : s ∈ Set.Icc (a : ℝ) (b : ℝ)
    · simp [hs,Real.volume_Ioo]
    · simp [hs]
  rw [hslice,lintegral_indicator measurableSet_Icc]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_surface lambda a b f)
    (Filter.Eventually.of_forall (surface_nonneg lambda f))).symm

theorem volume_region_ne_top (lambda : ℝ) (a b : ℝ≥0) (f : Path) :
    volume (region lambda a b f) ≠ ∞ := by
  rw [volume_region]
  exact ENNReal.ofReal_ne_top

theorem disjoint_regions_of_disjoint_intervals (lambda : ℝ) (f : Path)
    {a b c d : ℝ≥0}
    (h : Disjoint (Set.Icc (a : ℝ) (b : ℝ)) (Set.Icc (c : ℝ) (d : ℝ))) :
    Disjoint (region lambda a b f) (region lambda c d f) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact Set.disjoint_left.mp h hp.1 hq.1

end PerronWright.BrownianUnderGraphIntensity
