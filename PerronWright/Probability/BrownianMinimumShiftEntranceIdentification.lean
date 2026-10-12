import PerronWright.Probability.BrownianMinimumShiftOrderedSampling
import PerronWright.Probability.BrownianBridgeMinimumTimeWeakLimit
import PerronWright.Probability.BrownianEntranceSamplingUniqueness
import PerronWright.Probability.BrownianSmallMinimumTupleLaw

/-! # Actual minimum-shift and entrance continuous-path law identification

The ordered small-minimum-time density will be combined with the proved
actual path weak limit, then finite sampling and the genuine stopped-path
measurable embedding. No path-law or finite-dimensional identification is
assumed. The finite laws are obtained by uniqueness of the two limits of
the same actual small-minimum-time conditioned bridge.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumShiftEntranceIdentification

open BrownianPathLaw BrownianBridgeMinimumShift BrownianMinimumShiftOrderedSampling
open BrownianEntranceFiniteDimensionalFamily BrownianEntranceProjectiveFamily
open BrownianEntranceEndpointFamily BrownianEntranceCountableLaw
open BrownianEntranceContinuousRealization BrownianEntranceSamplingUniqueness
open BrownianBridgeMinimumTimeWeakLimit

theorem ae_minimumShiftLaw_initial_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂minimumShiftLaw T hT, f 0 = 0 := by
  apply (ae_map_iff (measurable_minimumShiftPath T hT).aemeasurable
    (measurableSet_eq_fun (continuous_eval 0).measurable measurable_const)).mpr
  exact Eventually.of_forall (minimumShiftPath_zero T hT)

theorem actual_minimumShift_orderedLaw (k : ℕ) (times : Fin (k+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0) :
    (minimumShiftLaw (times (Fin.last (k+1)))
      (by rw [← hzero]; exact hstrict (by simp only [Fin.lt_def,Fin.val_zero,Fin.val_last]; omega))).map (orderedEval k times) =
      orderedLaw k times := by
  have hT : 0 < times (Fin.last (k+1)) := by
    rw [← hzero]
    exact hstrict (by simp only [Fin.lt_def,Fin.val_zero,Fin.val_last]; omega)
  cases k with
  | zero =>
    have he : orderedEval 0 times = fun _ : Path ↦ (0 : Fin 0 → ℝ) :=
      funext (fun _ ↦ Subsingleton.elim _ _)
    rw [he,Measure.map_const,measure_univ,one_smul]
    rfl
  | succ n =>
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro Ψ
    have hmΨ : Measurable (fun v ↦ (Ψ v : ℝ≥0∞)) :=
      ENNReal.continuous_coe.measurable.comp Ψ.continuous.measurable
    rw [lintegral_map hmΨ (continuous_orderedEval (n+1) times).measurable]
    let F : Path →ᵇ ℝ≥0 := Ψ.compContinuous
      ⟨orderedEval (n+1) times,continuous_orderedEval (n+1) times⟩
    have hw := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp
      (tendsto_actual_smallMinimumProbability (times (Fin.last (n+2))) hT) F
    have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < (times (Fin.last (n+2)) : ℝ) :=
      (tendsto_id.mono_right nhdsWithin_le_nhds).eventually_lt_const hT
    have hw' : Tendsto (fun ε : ℝ ↦ ∫⁻ f,
        (Ψ (orderedEval (n+1) times f) : ℝ≥0∞)
          ∂BrownianBridgeMinimumTimeConditioning.smallMinimumLaw (times (Fin.last (n+2))) ε)
        (𝓝[>] 0) (𝓝 (∫⁻ f, (Ψ (orderedEval (n+1) times f) : ℝ≥0∞)
          ∂minimumShiftLaw (times (Fin.last (n+2))) hT)) := by
      apply hw.congr'
      filter_upwards [self_mem_nhdsWithin,hsmall] with ε hε hεT
      rw [smallMinimumProbability_toMeasure _ hT ε hε hεT.le]
      rfl
    have hd := BrownianSmallMinimumTupleLaw.actual_smallMinimum_ordered_test_tendsto
      n (tailTimes (n+1) times) (tailTimes_strictMono _ _ hstrict)
      (tailTimes_first_positive _ _ hstrict hzero) Ψ
    simp only [tailTimes_last,← orderedEval_tailTimes] at hd
    rw [BrownianMinimumTupleEndpointGeometry.fixedGaps,cons_tailTimes _ _ hzero] at hd
    rw [orderedLaw,BrownianPositiveBridgeMultiPointMass.entranceLaw,
      lintegral_withDensity_eq_lintegral_mul volume
        (BrownianPositiveBridgeMultiPointEntrance.measurable_entranceProduct n _) hmΨ]
    exact tendsto_nhds_unique hw' hd

theorem actual_minimumShift_interiorLaw (T : ℝ≥0) (hT : 0 < T)
    (J : Finset (InteriorTime T)) :
    (minimumShiftLaw T hT).map (BrownianEntranceProjectiveFamily.finiteEval T J) =
      BrownianEntranceProjectiveFamily.finiteLaw T J := by
  have h : (minimumShiftLaw T hT).map (orderedEval J.card (sortedTimes T J)) =
      orderedLaw J.card (sortedTimes T J) := by
    simpa only [sortedTimes_last] using actual_minimumShift_orderedLaw J.card (sortedTimes T J)
      (sortedTimes_strictMono T hT J) (sortedTimes_zero T J)
  have hm := congrArg (fun μ : Measure (Fin J.card → ℝ) ↦ μ.map (unsort T J)) h
  rw [Measure.map_map (measurable_unsort T J) (continuous_orderedEval _ _).measurable] at hm
  simpa only [Function.comp_def,unsort_orderedEval,BrownianEntranceProjectiveFamily.finiteLaw] using hm

theorem actual_minimumShift_paddedLaw (T : ℝ≥0) (hT : 0 < T) (J : Finset ℝ≥0) :
    (minimumShiftLaw T hT).map (paddedFiniteEval T J) =
      BrownianEntranceEndpointFamily.finiteLaw T J := by
  have h := congrArg (fun μ : Measure (insideTimes T J → ℝ) ↦ μ.map (pad T J))
    (actual_minimumShift_interiorLaw T hT (insideTimes T J))
  rw [Measure.map_map (measurable_pad T J) (continuous_finiteEval _ _).measurable] at h
  simpa only [Function.comp_def,pad_finiteEval,BrownianEntranceEndpointFamily.finiteLaw] using h

theorem actual_minimumShift_sampleLaw (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    (minimumShiftLaw T hT).map (sampleEval T σ J) = sampleLaw T σ J := by
  rw [sampleLaw,← actual_minimumShift_paddedLaw T hT,
    Measure.map_map (measurable_sampleFromFinite σ J) (measurable_paddedFiniteEval _ _)]
  rfl

theorem actual_minimumShift_sampling_finite (T : ℝ≥0) (hT : 0 < T) (J : Finset ℕ) :
    (minimumShiftLaw T hT).map (fun f ↦ J.restrict (pathSampling T f)) =
      sampleLaw T (BrownianEntranceDyadicSamples.samplingTimes T) J := by
  rw [← actual_minimumShift_sampleLaw T hT]
  apply Measure.map_congr
  filter_upwards [ae_minimumShiftLaw_initial_zero T hT,
    ae_minimumShiftLaw_stopped_zero T hT] with f hz hs
  funext j
  let t := BrownianEntranceDyadicSamples.samplingTimes T j.val
  change f t = if 0 < t ∧ t < T then f t else 0
  by_cases hi : 0 < t ∧ t < T
  · rw [if_pos hi]
  · rw [if_neg hi]
    by_cases ht : 0 < t
    · exact hs t (le_of_not_gt (fun h ↦ hi ⟨ht,h⟩))
    · rw [le_antisymm (le_of_not_gt ht) (zero_le : (0 : ℝ≥0) ≤ t)]
      exact hz

theorem actual_minimumShift_samplingLaw (T : ℝ≥0) (hT : 0 < T) :
    (minimumShiftLaw T hT).map (pathSampling T) = BrownianEntranceDyadicSamples.law T hT := by
  apply BrownianEntranceCountableLaw.law_unique
  intro J
  rw [Measure.map_map (Finset.measurable_restrict J) (measurable_pathSampling T)]
  exact actual_minimumShift_sampling_finite T hT J

/-- Genuine equality of the two compact-open Borel continuous-path laws.
The finite-dimensional identities are proved above from actual Brownian
conditioning and both genuine limits; none are hypotheses of this theorem. -/
theorem actual_minimumShiftLaw_eq_entrance (T : ℝ≥0) (hT : 0 < T) :
    minimumShiftLaw T hT = BrownianEntranceContinuousRealization.pathLaw T hT :=
  stopped_zero_law_eq_entrance_of_sampling T hT (minimumShiftLaw T hT)
    (ae_minimumShiftLaw_stopped_zero T hT) (actual_minimumShift_samplingLaw T hT)

end PerronWright.BrownianMinimumShiftEntranceIdentification
