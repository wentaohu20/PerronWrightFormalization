import PerronWright.Probability.BrownianSurvivalEntranceScaling
import PerronWright.Probability.BrownianFirstPassageBridgeLaw
import PerronWright.Probability.BrownianPathIndependentIncrements

/-! # Actual normalized survival restrictions retain a fresh whole future

Survival depends only on the literal stopped prefix. Restricting the
proved Brownian past/future product law and applying the literal scalar
normalization gives the whole normalized survival law by path splicing.
No entrance law, path convergence or conditional distribution is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianNormalizedSurvivalWholeLaw

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianSurvivalEntranceScaling

theorem survival_pastPath_preimage (delta : ℝ) (T : ℝ≥0) :
    (pastPath T) ⁻¹' survival (-delta) T = survival (-delta) T := by
  ext f
  exact BrownianFirstPassageBridgeLaw.stopped_mem_survival_iff (-delta) T f

theorem survival_restricted_past_law (delta : ℝ) (T : ℝ≥0) :
    (pathLaw.restrict (survival (-delta) T)).map (pastPath T) =
      (pastLaw T).restrict (survival (-delta) T) := by
  have he := Measure.restrict_map (μ := pathLaw) (measurable_pastPath T)
    (measurableSet_survival (-delta) T)
  rw [survival_pastPath_preimage] at he
  exact he.symm

theorem survival_restricted_past_future_jointLaw (delta : ℝ) (T : ℝ≥0) :
    (pathLaw.restrict (survival (-delta) T)).map
      (fun f ↦ (pastPath T f,futurePath T f)) =
      ((pastLaw T).restrict (survival (-delta) T)).prod pathLaw := by
  have hm := (measurable_pastPath T).prodMk (measurable_futurePath T)
  have hs : MeasurableSet (survival (-delta) T ×ˢ (univ : Set Path)) :=
    (measurableSet_survival (-delta) T).prod MeasurableSet.univ
  have he := Measure.restrict_map (μ := pathLaw) hm hs
  rw [past_future_jointLaw,← Measure.restrict_prod_eq_prod_univ] at he
  have hp : (fun f ↦ (pastPath T f,futurePath T f)) ⁻¹'
      (survival (-delta) T ×ˢ (univ : Set Path)) = survival (-delta) T := by
    ext f
    simp only [mem_preimage,mem_prod,mem_univ,and_true]
    exact BrownianFirstPassageBridgeLaw.stopped_mem_survival_iff (-delta) T f
  rw [hp] at he
  exact he.symm

theorem normalized_survival_isFinite (delta : ℝ) (hdelta : 0 < delta) (T : ℝ≥0) :
    IsFiniteMeasure (normalizedSurvivalLaw delta T) := by
  constructor
  rw [normalizedSurvivalLaw,Measure.smul_apply]
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hdelta))
    (measure_ne_top _ _))

theorem normalized_survival_past_future_jointLaw (delta : ℝ) (T : ℝ≥0) :
    (normalizedSurvivalLaw delta T).map (fun f ↦ (pastPath T f,futurePath T f)) =
      ((normalizedSurvivalLaw delta T).map (pastPath T)).prod pathLaw := by
  rw [normalizedSurvivalLaw,Measure.map_smul,Measure.map_smul,
    survival_restricted_past_future_jointLaw,survival_restricted_past_law,
    Measure.prod_smul_left]

theorem normalized_survival_whole_splice_law (delta : ℝ) (T : ℝ≥0) :
    (((normalizedSurvivalLaw delta T).map (pastPath T)).prod pathLaw).map (splicePath T) =
      normalizedSurvivalLaw delta T := by
  rw [← normalized_survival_past_future_jointLaw,
    Measure.map_map (measurable_splicePath T)
      ((measurable_pastPath T).prodMk (measurable_futurePath T))]
  have he : splicePath T ∘ (fun f : Path ↦ (pastPath T f,futurePath T f)) = id :=
    funext (fun f ↦ splice_past_future T f)
  rw [he,Measure.map_id]

theorem normalized_survival_whole_lintegral (delta : ℝ) (hdelta : 0 < delta) (T : ℝ≥0)
    {F : Path → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ f : Path, F f ∂normalizedSurvivalLaw delta T) =
      ∫⁻ p : Path, ∫⁻ h : Path, F (splicePath T (p,h)) ∂pathLaw
        ∂(normalizedSurvivalLaw delta T).map (pastPath T) := by
  let := normalized_survival_isFinite delta hdelta T
  let : IsFiniteMeasure ((normalizedSurvivalLaw delta T).map (pastPath T)) :=
    Measure.isFiniteMeasure_map (normalizedSurvivalLaw delta T) (pastPath T)
  calc
    _ = ∫⁻ f : Path, F f
        ∂(((normalizedSurvivalLaw delta T).map (pastPath T)).prod pathLaw).map
          (splicePath T) := by rw [normalized_survival_whole_splice_law]
    _ = ∫⁻ p : Path × Path, F (splicePath T p)
        ∂((normalizedSurvivalLaw delta T).map (pastPath T)).prod pathLaw :=
      lintegral_map hF (measurable_splicePath T)
    _ = _ := lintegral_prod _ (hF.comp (measurable_splicePath T)).aemeasurable

end PerronWright.BrownianNormalizedSurvivalWholeLaw
