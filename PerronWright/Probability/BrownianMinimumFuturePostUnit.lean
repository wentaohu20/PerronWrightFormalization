import PerronWright.Probability.BrownianMinimumFutureEntranceSource
import PerronWright.Probability.BrownianMinimumEndpointPinningGeometry
import PerronWright.Probability.BrownianFirstPassagePastFibers

/-! # Genuine post-unit Brownian future of the minimum-future source

The rescaled source prefix depends only on the original unit past.
Its whole post-unit future is a randomly dilated fresh Brownian path.
Random dilation invariance is derived from the actual path law, not
supplied as a conditional distribution assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMinimumFuturePostUnit

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathDilationLaw
open BrownianMinimumFutureEntranceSource ContinuousPathLeastMinimum

theorem measurable_joint_brownianDilation :
    Measurable (fun p : ℝ≥0 × Path ↦ brownianDilation p.1 p.2) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  apply measurable_pi_lambda
  intro q
  have ht : Measurable (fun p : ℝ≥0 × Path ↦
      BrownianGaussianSkeleton.rationalTimeReal q/p.1) := measurable_const.div measurable_fst
  have he := continuous_joint_eval.measurable.comp (measurable_snd.prodMk ht)
  have hs : Measurable (fun p : ℝ≥0 × Path ↦ Real.sqrt (p.1 : ℝ)) :=
    Real.continuous_sqrt.measurable.comp
    (NNReal.continuous_coe.measurable.comp measurable_fst)
  exact hs.mul he

theorem random_brownianDilation_jointLaw {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {c : X → ℝ≥0} (hc : Measurable c)
    (hpos : ∀ᵐ x ∂μ, 0 < c x) :
    (μ.prod pathLaw).map (fun p ↦ (p.1,brownianDilation (c p.1) p.2)) =
      μ.prod pathLaw := by
  have hj : Measurable (fun p : X × Path ↦ (p.1,brownianDilation (c p.1) p.2)) :=
    measurable_fst.prodMk (measurable_joint_brownianDilation.comp
      ((hc.comp measurable_fst).prodMk measurable_snd))
  apply Measure.ext_of_lintegral
  intro Φ hΦ
  rw [lintegral_map hΦ hj]
  have hl := lintegral_prod (μ := μ) (ν := pathLaw)
    (fun p : X × Path ↦ Φ (p.1,brownianDilation (c p.1) p.2))
    (hΦ.comp hj).aemeasurable
  rw [hl,lintegral_prod _ hΦ.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hpos] with x hx
  have hm : Measurable (fun g : Path ↦ Φ (x,g)) :=
    hΦ.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_map hm (measurable_brownianDilation (c x)),
    pathLaw_brownianDilation (c x) hx]

theorem leastMinimizer_pastPath (f : Path) :
    leastMinimizer 1 (pastPath 1 f) = leastMinimizer 1 f := by
  have h := BrownianMinimumEndpointPinningGeometry.minimumTriple_stoppedPath 1 f
  exact congrArg Prod.fst h

theorem remainingDuration_pastPath (f : Path) :
    remainingDuration (pastPath 1 f) = remainingDuration f := by
  simp only [remainingDuration,leastMinimizer_pastPath]

theorem source_prefix_pastPath (f : Path) :
    pastPath 1 (unitMinimumFuture (pastPath 1 f)) =
      pastPath 1 (unitMinimumFuture f) := by
  apply ContinuousMap.ext
  intro t
  rw [pastPath_eval,pastPath_eval]
  change (pastPath 1 f (leastMinimizer 1 (pastPath 1 f)+
      remainingDuration (pastPath 1 f)*min t 1)-
      pastPath 1 f (leastMinimizer 1 (pastPath 1 f)))/
      Real.sqrt (remainingDuration (pastPath 1 f) : ℝ) = _
  rw [leastMinimizer_pastPath,remainingDuration_pastPath,pastPath_eval,pastPath_eval]
  have ht : leastMinimizer 1 f+remainingDuration f*min t 1 ≤ 1 := by
    calc
      _ ≤ leastMinimizer 1 f+remainingDuration f*1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (min_le_right t 1) bot_le)
      _ = 1 := by
        rw [mul_one,remainingDuration,add_tsub_cancel_of_le (leastMinimizer_le_time 1 f)]
  rw [min_eq_left ht,min_eq_left (leastMinimizer_le_time 1 f)]
  rfl

theorem source_future_brownianDilation (f : Path) :
    futurePath 1 (unitMinimumFuture f) =
      brownianDilation (remainingDuration f)⁻¹ (futurePath 1 f) := by
  apply ContinuousMap.ext
  intro t
  have ht : leastMinimizer 1 f+remainingDuration f = 1 := by
    rw [remainingDuration,add_tsub_cancel_of_le (leastMinimizer_le_time 1 f)]
  have htime : leastMinimizer 1 f+remainingDuration f*(1+t) =
      1+remainingDuration f*t := by rw [mul_add,mul_one,← add_assoc,ht]
  change (unitMinimumFuture f (1+t)-unitMinimumFuture f 1) = _
  change ((f (leastMinimizer 1 f+remainingDuration f*(1+t))-
      f (leastMinimizer 1 f))/Real.sqrt (remainingDuration f : ℝ)-
      (f (leastMinimizer 1 f+remainingDuration f*1)-f (leastMinimizer 1 f))/
      Real.sqrt (remainingDuration f : ℝ)) =
      Real.sqrt ((remainingDuration f)⁻¹ : ℝ≥0)*
        (f (1+t/(remainingDuration f)⁻¹)-f 1)
  rw [htime,mul_one,ht,NNReal.coe_inv,Real.sqrt_inv,div_inv_eq_mul]
  rw [mul_comm t]
  ring

theorem actual_source_past_future_jointLaw :
    unitSourceLaw.map (fun g ↦ (pastPath 1 g,futurePath 1 g)) =
      (unitSourceLaw.map (pastPath 1)).prod pathLaw := by
  let A : Path → Path := fun p ↦ pastPath 1 (unitMinimumFuture p)
  let c : Path → ℝ≥0 := fun p ↦ (remainingDuration p)⁻¹
  let R : Path × Path → Path × Path := fun p ↦ (p.1,brownianDilation (c p.1) p.2)
  let Z : Path × Path → Path × Path := fun p ↦ (A p.1,brownianDilation (c p.1) p.2)
  have hA : Measurable A := (measurable_pastPath 1).comp measurable_unitMinimumFuture
  have hc : Measurable c := measurable_remainingDuration.inv
  have hR : Measurable R := measurable_fst.prodMk
    (measurable_joint_brownianDilation.comp ((hc.comp measurable_fst).prodMk measurable_snd))
  have hZ : Measurable Z := (hA.comp measurable_fst).prodMk
    (measurable_joint_brownianDilation.comp ((hc.comp measurable_fst).prodMk measurable_snd))
  have he : (fun f : Path ↦ (pastPath 1 (unitMinimumFuture f),
      futurePath 1 (unitMinimumFuture f))) =
      Z ∘ (fun f : Path ↦ (pastPath 1 f,futurePath 1 f)) := by
    funext f
    change (_,_) = (pastPath 1 (unitMinimumFuture (pastPath 1 f)),
      brownianDilation (remainingDuration (pastPath 1 f))⁻¹ (futurePath 1 f))
    rw [source_prefix_pastPath,remainingDuration_pastPath,source_future_brownianDilation]
  have hpos : ∀ᵐ p ∂pastLaw 1, 0 < c p := by
    rw [pastLaw]
    apply (ae_map_iff (measurable_pastPath 1).aemeasurable
      (measurableSet_lt measurable_const hc)).mpr
    filter_upwards [ae_remainingDuration_pos] with f hf
    change 0 < (remainingDuration (pastPath 1 f))⁻¹
    rw [remainingDuration_pastPath]
    exact inv_pos.mpr hf
  have hprefix : (pastLaw 1).map A = unitSourceLaw.map (pastPath 1) := by
    rw [pastLaw,unitSourceLaw,Measure.map_map hA (measurable_pastPath 1),
      Measure.map_map (measurable_pastPath 1) measurable_unitMinimumFuture]
    congr 1
    funext f
    exact source_prefix_pastPath f
  rw [unitSourceLaw,Measure.map_map
    ((measurable_pastPath 1).prodMk (measurable_futurePath 1)) measurable_unitMinimumFuture]
  change pathLaw.map (fun f ↦ (pastPath 1 (unitMinimumFuture f),
    futurePath 1 (unitMinimumFuture f))) = _
  rw [he,← Measure.map_map hZ ((measurable_pastPath 1).prodMk (measurable_futurePath 1)),
    past_future_jointLaw]
  have hZeq : Z = Prod.map A (id : Path → Path) ∘ R := rfl
  rw [hZeq,← Measure.map_map (hA.prodMap measurable_id) hR,
    random_brownianDilation_jointLaw (pastLaw 1) hc hpos,
    ← Measure.map_prod_map (pastLaw 1) pathLaw hA measurable_id,Measure.map_id,hprefix]
  rfl

end PerronWright.BrownianMinimumFuturePostUnit
