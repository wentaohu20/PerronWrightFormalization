import PerronWright.Probability.BrownianParabolicDriftTilt
import PerronWright.Probability.BrownianPathReflectionLaw
import PerronWright.Probability.BrownianMinimumEndpointPinningGeometry
import PerronWright.Probability.BrownianMinimumSplitWindowActualLimit

/-! # Actual parabolic prefix minima and their full path split

The proved stopped parabolic Radon--Nikodym law transfers the genuine
Brownian negative/interior minimum event. Deterministic first-hit bands
and dominated convergence then retain the entire stopped past and the
entire future of the actual parabolic driver. No minimum geometry or
conditional-law premise is supplied.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicMinimumSplitWindow

open BrownianPathLaw ContinuousPathLeastMinimum BrownianPathReflectionLaw
open BrownianParabolicDriftTiltGeometry BrownianParabolicDriftTilt
open BrownianMinimumSplitWindowActualLimit ContinuousPathMinimumSplitBandAverage

private theorem minimum_geometry_stopped (T : ℝ≥0) (f : Path) :
    minimumValue T (BrownianEndpointDriftTilt.stoppedPath T f) = minimumValue T f ∧
      leastMinimizer T (BrownianEndpointDriftTilt.stoppedPath T f) = leastMinimizer T f := by
  have h := BrownianMinimumEndpointPinningGeometry.minimumTriple_stoppedPath T f
  exact ⟨congrArg (fun p : ℝ≥0 × ℝ × ℝ ↦ p.2.1) h,congrArg Prod.fst h⟩

theorem ae_actual_minimum_geometry (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, minimumValue T (driftPath lambda f) < 0 ∧
      0 < leastMinimizer T (driftPath lambda f) ∧ leastMinimizer T (driftPath lambda f) < T := by
  let P : Path → Prop := fun f ↦ minimumValue T f < 0 ∧
    0 < leastMinimizer T f ∧ leastMinimizer T f < T
  have hP : MeasurableSet {f : Path | P f} :=
    ((continuous_minimumValue T).measurable measurableSet_Iio).inter
      (((measurable_leastMinimizer T) measurableSet_Ioi).inter
        ((measurable_leastMinimizer T) measurableSet_Iio))
  have hs (f : Path) : P (BrownianEndpointDriftTilt.stoppedPath T f) ↔ P f := by
    dsimp only [P]
    rw [(minimum_geometry_stopped T f).1,(minimum_geometry_stopped T f).2]
  have hb : ∀ᵐ f ∂pathLaw, P f := by
    filter_upwards [BrownianMinimumNegative.ae_minimumValue_negative T hT,
      BrownianPathFiniteReversal.ae_leastMinimizer_interior T hT] with f hn hi
    exact ⟨hn,hi⟩
  have hw : ∀ᵐ f ∂pathLaw.withDensity (density lambda T), P f :=
    (withDensity_absolutelyContinuous pathLaw (density lambda T)).ae_le hb
  have hstop : ∀ᵐ f ∂(pathLaw.withDensity (density lambda T)).map
      (BrownianEndpointDriftTilt.stoppedPath T), P f :=
    (ae_map_iff (BrownianEndpointDriftTilt.measurable_stoppedPath T).aemeasurable hP).mpr
      (hw.mono (fun f hf ↦ (hs f).mpr hf))
  rw [← actual_stopped_parabolic_law_eq_weighted lambda T hT] at hstop
  have hd := (ae_map_iff (measurable_stoppedParabolicPath lambda T).aemeasurable hP).mp hstop
  filter_upwards [hd] with f hf
  have he : BrownianEndpointDriftTilt.stoppedPath T (driftPath lambda f) =
      stoppedParabolicPath lambda T f := by
    apply ContinuousMap.ext
    intro t
    rfl
  exact (hs (driftPath lambda f)).mp (he.symm ▸ hf)

theorem ae_actual_minimum_lt_start (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, minimumValue T (driftPath lambda f) < driftPath lambda f 0 := by
  filter_upwards [ae_actual_minimum_geometry lambda T hT,
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf hz
  simpa only [driftPath_apply,NNReal.coe_zero,mul_zero,zero_pow (by norm_num : 2 ≠ 0),
    zero_div,add_zero,sub_zero,hz] using hf.1

theorem actual_parabolic_level_window_split_limit (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) :
    Tendsto (fun δ : ℝ ↦ ∫ f, levelWindowAverage T Ψ δ (driftPath lambda f) ∂pathLaw)
      (𝓝[>] 0) (𝓝 (∫ f, Ψ (minimumPoint T (driftPath lambda f)) ∂pathLaw)) := by
  have hm : Measurable (driftPath lambda) :=
    (continuous_driftPath.comp (continuous_const.prodMk continuous_id)).measurable
  have ht : Tendsto (fun δ : ℝ ↦ ∫ f, truncatedUnitBandAverage T Ψ δ (driftPath lambda f) ∂pathLaw)
      (𝓝[>] 0) (𝓝 (∫ f, Ψ (minimumPoint T (driftPath lambda f)) ∂pathLaw)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖Ψ‖)
    · exact Eventually.of_forall (fun δ ↦ ((measurable_truncatedUnitBandAverage T Ψ).comp
        (measurable_const.prodMk hm)).aestronglyMeasurable)
    · exact Eventually.of_forall (fun δ ↦ Eventually.of_forall (fun f ↦
        norm_truncatedUnitBandAverage_le T Ψ δ (driftPath lambda f)))
    · exact integrable_const ‖Ψ‖
    · filter_upwards [ae_actual_minimum_geometry lambda T hT,
        ae_actual_minimum_lt_start lambda T hT] with f hf hs
      apply (tendsto_unitBandAverage T (driftPath lambda f) hs Ψ).congr'
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (neg_pos.mpr hf.1)).filter_mono nhdsWithin_le_nhds]
        with δ hδ hdepth
      exact (truncatedUnitBandAverage_eq_unit T Ψ δ hδ (driftPath lambda f) hdepth).symm
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  apply (integral_congr_ae _).symm
  filter_upwards [ae_actual_minimum_geometry lambda T hT] with f hf
  exact levelWindowAverage_eq_truncated T Ψ δ hδ (driftPath lambda f) hf.2.2

end PerronWright.BrownianParabolicMinimumSplitWindow
