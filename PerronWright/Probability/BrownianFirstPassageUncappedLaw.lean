import PerronWright.Probability.BrownianFirstPassageStrongMarkov

/-! # Whole-path first-passage factorization from actual bounded laws

The bounded first-passage product law passes to an almost surely finite
uncapped passage by bounded continuous tests. The finiteness assumption
in this intermediate lemma will be discharged for the actual Brownian law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFirstPassageUncappedLaw

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassageReflection BrownianFirstPassagePastFibers
open BrownianFirstPassageStrongMarkov

theorem tendsto_map_pathLaw_of_ae {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (F : ℕ → Path → X) (f : Path → X)
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f)
    (hlim : ∀ᵐ g ∂pathLaw, Tendsto (fun n ↦ F n g) atTop (𝓝 (f g))) :
    Tendsto (fun n ↦ brownianProbability.map (hF n).aemeasurable) atTop
      (𝓝 (brownianProbability.map hf.aemeasurable)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro Ψ
  have he (n : ℕ) : (∫ x, Ψ x ∂(brownianProbability.map (hF n).aemeasurable : Measure X)) =
      ∫ g, Ψ (F n g) ∂pathLaw :=
    integral_map (hF n).aemeasurable Ψ.continuous.measurable.aestronglyMeasurable
  have ht : (∫ x, Ψ x ∂(brownianProbability.map hf.aemeasurable : Measure X)) =
      ∫ g, Ψ (f g) ∂pathLaw :=
    integral_map hf.aemeasurable Ψ.continuous.measurable.aestronglyMeasurable
  simp only [he,ht]
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ ‖Ψ‖)
  · intro n
    exact (Ψ.continuous.measurable.comp (hF n)).aestronglyMeasurable
  · exact integrable_const ‖Ψ‖
  · exact fun _ ↦ Eventually.of_forall (fun g ↦ Ψ.norm_coe_le_norm _)
  · filter_upwards [hlim] with g hg
    exact Ψ.continuous.tendsto _ |>.comp hg

def passageTime (level : ℝ) (f : Path) : ℝ≥0 := (firstPassage level f).toNNReal

def passagePast (level : ℝ) (f : Path) : ℝ≥0 × Path :=
  (passageTime level f,pastPath (passageTime level f) f)

def passageFuture (level : ℝ) (f : Path) : Path := futurePath (passageTime level f) f

theorem measurable_passageTime (level : ℝ) : Measurable (passageTime level) :=
  (measurable_firstPassage level).ennreal_toNNReal

theorem measurable_passagePast (level : ℝ) : Measurable (passagePast level) :=
  (measurable_passageTime level).prodMk (continuous_joint_pastPath.measurable.comp
    ((measurable_passageTime level).prodMk measurable_id))

theorem measurable_passageFuture (level : ℝ) : Measurable (passageFuture level) :=
  continuous_joint_futurePath.measurable.comp
    ((measurable_passageTime level).prodMk measurable_id)

theorem cappedTime_eventually_eq (level : ℝ) (f : Path)
    (hfinite : firstPassage level f ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, cappedTime level (n : ℝ≥0) f = passageTime level f := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((passageTime level f : ℝ≥0) : ℝ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hb : passageTime level f ≤ (n : ℝ≥0) := by
    have hc : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact_mod_cast (le_trans hN.le hc)
  apply ENNReal.coe_injective
  rw [cappedTime_coe]
  change min (firstPassage level f) (n : ℝ≥0∞) =
    ((firstPassage level f).toNNReal : ℝ≥0∞)
  rw [ENNReal.coe_toNNReal hfinite]
  apply min_eq_left
  rw [← ENNReal.coe_toNNReal hfinite]
  exact ENNReal.coe_le_coe.mpr hb

theorem boundedPast_tendsto (level : ℝ) (f : Path)
    (hfinite : firstPassage level f ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ boundedPast level (n : ℝ≥0) f) atTop
      (𝓝 (passagePast level f)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [cappedTime_eventually_eq level f hfinite] with n hn
  simp only [boundedPast,passagePast,hn]

theorem boundedFuture_tendsto (level : ℝ) (f : Path)
    (hfinite : firstPassage level f ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ boundedFuture level (n : ℝ≥0) f) atTop
      (𝓝 (passageFuture level f)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [cappedTime_eventually_eq level f hfinite] with n hn
  simp only [boundedFuture,passageFuture,hn]

theorem passage_jointLaw_of_ae_finite (level : ℝ)
    (hfinite : ∀ᵐ f ∂pathLaw, firstPassage level f ≠ ⊤) :
    pathLaw.map (fun f ↦ (passagePast level f,passageFuture level f)) =
      (pathLaw.map (passagePast level)).prod pathLaw := by
  have hp := measurable_passagePast level
  have hf := measurable_passageFuture level
  have hwp := tendsto_map_pathLaw_of_ae
    (fun n ↦ boundedPast level (n : ℝ≥0)) (passagePast level)
    (fun n ↦ measurable_boundedPast _ _) hp
    (hfinite.mono (fun f hf ↦ boundedPast_tendsto level f hf))
  have hwj := tendsto_map_pathLaw_of_ae
    (fun n f ↦ (boundedPast level (n : ℝ≥0) f,boundedFuture level (n : ℝ≥0) f))
    (fun f ↦ (passagePast level f,passageFuture level f))
    (fun n ↦ (measurable_boundedPast _ _).prodMk (measurable_boundedFuture _ _))
    (hp.prodMk hf) (hfinite.mono (fun f hf ↦
      (boundedPast_tendsto level f hf).prodMk_nhds (boundedFuture_tendsto level f hf)))
  have hwprod := ProbabilityMeasure.continuous_prod.tendsto
    (brownianProbability.map hp.aemeasurable,brownianProbability) |>.comp
      (hwp.prodMk_nhds tendsto_const_nhds)
  have he (n : ℕ) : brownianProbability.map
      ((measurable_boundedPast level (n : ℝ≥0)).prodMk
        (measurable_boundedFuture level (n : ℝ≥0))).aemeasurable =
      ProbabilityMeasure.prod
        (brownianProbability.map (measurable_boundedPast level (n : ℝ≥0)).aemeasurable)
        brownianProbability := by
    apply Subtype.ext
    exact bounded_jointLaw level (n : ℝ≥0)
  exact congrArg ProbabilityMeasure.toMeasure
    (tendsto_nhds_unique hwj (hwprod.congr' (Eventually.of_forall (fun n ↦ (he n).symm))))

end PerronWright.BrownianFirstPassageUncappedLaw
