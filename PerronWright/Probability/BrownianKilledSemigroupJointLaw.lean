import PerronWright.Probability.BrownianKilledSemigroup
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Actual two-segment killed endpoint joint law

The surviving pair of actual Brownian endpoints has exactly the killed
head endpoint law times the genuine killed future transition kernel.
This is a Borel measure identity, hence gives every coupled nonnegative
endpoint test and every two-endpoint rectangle without a moment premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledSemigroupJointLaw

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianKilledTransitionKernel BrownianKilledSemigroup

def survivingPairLaw (level : ℝ) (s t : ℝ≥0) : Measure (ℝ × ℝ) :=
  (pathLaw.restrict (survival level (s+t))).map (fun f : Path ↦ (f s,f (s+t)))

instance survivingPairLaw_isFinite (level : ℝ) (s t : ℝ≥0) :
    IsFiniteMeasure (survivingPairLaw level s t) := by
  unfold survivingPairLaw
  infer_instance

theorem survivingPairLaw_apply (level : ℝ) (s t : ℝ≥0)
    {D : Set (ℝ × ℝ)} (hD : MeasurableSet D) :
    survivingPairLaw level s t D =
      pathLaw {f : Path | f ∈ survival level (s+t) ∧ (f s,f (s+t)) ∈ D} := by
  have hm : Measurable (fun f : Path ↦ (f s,f (s+t))) :=
    (continuous_eval s).measurable.prodMk (continuous_eval (s+t)).measurable
  rw [survivingPairLaw,Measure.map_apply hm hD,Measure.restrict_apply (hm hD)]
  congr 1
  ext f
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
  exact and_comm

def pairEvent (level : ℝ) (s t : ℝ≥0) (D : Set (ℝ × ℝ)) : Set (Path × Path) :=
  {p | p.1 ∈ survival level s ∧ p.2 ∈ survival (level-p.1 s) t ∧
    (p.1 s,p.1 s+p.2 t) ∈ D}

theorem measurableSet_pairEvent (level : ℝ) (s t : ℝ≥0)
    {D : Set (ℝ × ℝ)} (hD : MeasurableSet D) : MeasurableSet (pairEvent level s t D) := by
  have hx : Continuous (fun p : Path × Path ↦ p.1 s) :=
    (continuous_eval s).comp continuous_fst
  have hy : Continuous (fun p : Path × Path ↦ p.2 t) :=
    (continuous_eval t).comp continuous_snd
  exact (measurable_fst (measurableSet_survival level s)).inter
    (((isOpen_lt (continuous_const.sub hx)
      ((continuous_minimum_at t).comp continuous_snd)).measurableSet).inter
      ((hx.prodMk (hx.add hy)).measurable hD))

theorem pairEvent_preimage (level : ℝ) (s t : ℝ≥0) (D : Set (ℝ × ℝ)) :
    (fun f : Path ↦ (pastPath s f,futurePath s f)) ⁻¹' pairEvent level s t D =
      {f : Path | f ∈ survival level (s+t) ∧ (f s,f (s+t)) ∈ D} := by
  ext f
  simp only [mem_preimage,pairEvent,mem_ofPred_eq,pastPath_eval,min_self,
    past_survival_iff,survival_add_iff,endpoint_add]
  exact and_assoc.symm

/-- Literal actual Brownian two-endpoint disintegration, including the
survival gate on both consecutive segments. -/
theorem survivingPairLaw_eq_compProd (level : ℝ) (s t : ℝ≥0) :
    survivingPairLaw level s t = (killedEndpointLaw level s) ⊗ₘ killedKernel level t := by
  ext D hD
  have hm : Measurable (fun x : ℝ ↦ killedKernel level t x ((fun y : ℝ ↦ (x,y)) ⁻¹' D)) :=
    (killedKernel level t).measurable_kernel_prodMk_left hD
  rw [Measure.compProd_apply hD,← lintegral_past_survival_eq_killed level s hm]
  let A := pairEvent level s t D
  have hA : MeasurableSet A := measurableSet_pairEvent level s t hD
  have hj : Measurable (fun f : Path ↦ (pastPath s f,futurePath s f)) :=
    (measurable_pastPath s).prodMk (measurable_futurePath s)
  have he : survivingPairLaw level s t D = ((pastLaw s).prod pathLaw) A := by
    rw [← past_future_jointLaw s,Measure.map_apply hj hA,pairEvent_preimage,
      survivingPairLaw_apply level s t hD]
  rw [he,Measure.prod_apply hA,← lintegral_indicator (measurableSet_survival level s)]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ survival level s
  · have hxD : MeasurableSet ((fun y : ℝ ↦ (p s,y)) ⁻¹' D) :=
      (measurable_const.prodMk measurable_id) hD
    rw [indicator_of_mem hp,killedKernel_apply,transitionLaw_apply level t (p s) hxD]
    congr 1
    ext g
    simp only [A,pairEvent,tailEvent,mem_preimage,mem_ofPred_eq,hp,true_and]
  · have he : (fun g : Path ↦ (p,g)) ⁻¹' A = ∅ := by
      ext g
      simp only [A,pairEvent,mem_preimage,mem_ofPred_eq,hp,false_and,mem_empty_iff_false]
    rw [he,measure_empty,indicator_of_notMem hp]

theorem two_endpoint_rectangle_probability (level : ℝ) (s t : ℝ≥0)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    pathLaw {f : Path | f ∈ survival level (s+t) ∧ f s ∈ A ∧ f (s+t) ∈ B} =
      ∫⁻ x in A, transitionLaw level t x B ∂killedEndpointLaw level s := by
  have he : {f : Path | f ∈ survival level (s+t) ∧ f s ∈ A ∧ f (s+t) ∈ B} =
      {f : Path | f ∈ survival level (s+t) ∧ (f s,f (s+t)) ∈ A ×ˢ B} := by
    ext f
    simp only [mem_ofPred_eq,mem_prod]
  rw [he,← survivingPairLaw_apply level s t (hA.prod hB),survivingPairLaw_eq_compProd,
    Measure.compProd_apply_prod hA hB]
  rfl

theorem lintegral_surviving_pair (level : ℝ) (s t : ℝ≥0)
    {Φ : ℝ × ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f in survival level (s+t), Φ (f s,f (s+t)) ∂pathLaw) =
      ∫⁻ x, ∫⁻ y, Φ (x,y) ∂transitionLaw level t x ∂killedEndpointLaw level s := by
  have hj : Measurable (fun f : Path ↦ (f s,f (s+t))) :=
    (continuous_eval s).measurable.prodMk (continuous_eval (s+t)).measurable
  rw [← lintegral_map hΦ hj]
  change (∫⁻ p, Φ p ∂survivingPairLaw level s t) = _
  rw [survivingPairLaw_eq_compProd]
  exact Measure.lintegral_compProd hΦ

end PerronWright.BrownianKilledSemigroupJointLaw
