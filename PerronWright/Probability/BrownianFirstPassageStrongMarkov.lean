import PerronWright.Probability.BrownianFirstPassageGridStrongMarkov
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-! # Actual Brownian whole-path factorization at bounded first passage

The existing literal first-passage grid times converge to the bounded
passage time for every continuous path. Joint path continuity and bounded
continuous tests pass the proved grid product law to the limit. The
result is a genuine stopped-time path-law identity, not a strong-Markov
interface assumed for the Brownian law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFirstPassageStrongMarkov

open BrownianPathLaw BrownianPathIndependentIncrements BrownianFirstPassageReflection
open BrownianFirstPassageGridReflection BrownianFirstPassagePastFibers
open BrownianFirstPassageGridStrongMarkov DyadicFloorGeometry

def brownianProbability : ProbabilityMeasure Path := ⟨pathLaw,inferInstance⟩

theorem tendsto_map_pathLaw_of_pointwise {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (F : ℕ → Path → X) (f : Path → X)
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f)
    (hlim : ∀ g : Path, Tendsto (fun n ↦ F n g) atTop (𝓝 (f g))) :
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
  · exact Eventually.of_forall (fun g ↦ Ψ.continuous.tendsto _ |>.comp (hlim g))

def boundedPast (level : ℝ) (T : ℝ≥0) (f : Path) : ℝ≥0 × Path :=
  (cappedTime level T f,pastPath (cappedTime level T f) f)

def boundedFuture (level : ℝ) (T : ℝ≥0) (f : Path) : Path :=
  futurePath (cappedTime level T f) f

theorem measurable_boundedPast (level : ℝ) (T : ℝ≥0) : Measurable (boundedPast level T) :=
  (measurable_cappedTime level T).prodMk (continuous_joint_pastPath.measurable.comp
    ((measurable_cappedTime level T).prodMk measurable_id))

theorem measurable_boundedFuture (level : ℝ) (T : ℝ≥0) : Measurable (boundedFuture level T) :=
  continuous_joint_futurePath.measurable.comp
    ((measurable_cappedTime level T).prodMk measurable_id)

theorem dyadic_selectedPast_tendsto (level : ℝ) (T : ℝ≥0) (f : Path) :
    Tendsto (fun n ↦ selectedPast level (dyadicGrid n) (index n T) f) atTop
      (𝓝 (boundedPast level T f)) := by
  have ht := dyadic_selectedTime_tendsto level T f
  exact ht.prodMk_nhds (continuous_joint_pastPath.tendsto _ |>.comp
    (ht.prodMk_nhds tendsto_const_nhds))

theorem dyadic_selectedFuture_tendsto (level : ℝ) (T : ℝ≥0) (f : Path) :
    Tendsto (fun n ↦ selectedFuture level (dyadicGrid n) (index n T) f) atTop
      (𝓝 (boundedFuture level T f)) :=
  continuous_joint_futurePath.tendsto _ |>.comp
    ((dyadic_selectedTime_tendsto level T f).prodMk_nhds tendsto_const_nhds)

theorem bounded_jointLaw (level : ℝ) (T : ℝ≥0) :
    pathLaw.map (fun f ↦ (boundedPast level T f,boundedFuture level T f)) =
      (pathLaw.map (boundedPast level T)).prod pathLaw := by
  have hp := measurable_boundedPast level T
  have hf := measurable_boundedFuture level T
  have hj : Measurable (fun f ↦ (boundedPast level T f,boundedFuture level T f)) := hp.prodMk hf
  have hwp := tendsto_map_pathLaw_of_pointwise
    (fun n ↦ selectedPast level (dyadicGrid n) (index n T)) (boundedPast level T)
    (fun n ↦ measurable_selectedPast _ _ _) hp (dyadic_selectedPast_tendsto level T)
  have hwj := tendsto_map_pathLaw_of_pointwise
    (fun n f ↦ (selectedPast level (dyadicGrid n) (index n T) f,
      selectedFuture level (dyadicGrid n) (index n T) f))
    (fun f ↦ (boundedPast level T f,boundedFuture level T f))
    (fun n ↦ (measurable_selectedPast _ _ _).prodMk (measurable_selectedFuture _ _ _)) hj
    (fun f ↦ (dyadic_selectedPast_tendsto level T f).prodMk_nhds
      (dyadic_selectedFuture_tendsto level T f))
  have hwprod := ProbabilityMeasure.continuous_prod.tendsto
    (brownianProbability.map hp.aemeasurable,brownianProbability) |>.comp
      (hwp.prodMk_nhds tendsto_const_nhds)
  have he (n : ℕ) : brownianProbability.map
      ((measurable_selectedPast level (dyadicGrid n) (index n T)).prodMk
        (measurable_selectedFuture level (dyadicGrid n) (index n T))).aemeasurable =
      ProbabilityMeasure.prod
        (brownianProbability.map (measurable_selectedPast level (dyadicGrid n) (index n T)).aemeasurable)
        brownianProbability := by
    apply Subtype.ext
    exact selected_jointLaw level (dyadicGrid n) (monotone_dyadicGrid n) (index n T)
  exact congrArg ProbabilityMeasure.toMeasure
    (tendsto_nhds_unique hwj (hwprod.congr' (Eventually.of_forall (fun n ↦ (he n).symm))))

theorem boundedFuture_law (level : ℝ) (T : ℝ≥0) :
    pathLaw.map (boundedFuture level T) = pathLaw := by
  have hp := measurable_boundedPast level T
  have hf := measurable_boundedFuture level T
  let : IsProbabilityMeasure (pathLaw.map (boundedPast level T)) :=
    Measure.isProbabilityMeasure_map hp.aemeasurable
  have he := congrArg (Measure.map Prod.snd) (bounded_jointLaw level T)
  rw [Measure.map_map measurable_snd (hp.prodMk hf),Measure.map_snd_prod,
    measure_univ,one_smul] at he
  exact he

theorem boundedPast_future_independent (level : ℝ) (T : ℝ≥0) :
    IndepFun (boundedPast level T) (boundedFuture level T) pathLaw := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_boundedPast level T).aemeasurable
    (measurable_boundedFuture level T).aemeasurable).mpr
  rw [boundedFuture_law]
  exact bounded_jointLaw level T

end PerronWright.BrownianFirstPassageStrongMarkov
