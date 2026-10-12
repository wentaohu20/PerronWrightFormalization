import PerronWright.Probability.BrownianEntranceDyadicMoments
import PerronWright.Probability.FourthMomentDyadicModulus

/-! # A constructed continuous realization of the genuine entrance law

The actual transferred fourth moments imply the neighbor bounds almost
surely. Together with the proved almost-sure sampling compatibility these
bounds construct the continuous extension. Path-valued measurability uses
the proved compact-open Borel / countable-evaluation embedding. Its exact
countable sampling law is the original constructed entrance law.

This does not identify the law with a minimum-shift or conditioned-excursion
path law, and does not assume such an identity or a path weak limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceContinuousRealization

open BrownianPathLaw BrownianEntranceDyadicSamples BrownianEntranceDyadicMoments
open DyadicFloorGeometry DyadicGeometricApproximation DyadicGeometricExtension

def process (t : ℝ≥0) (x : ℕ → ℝ) : ℝ := extension (BrownianEntranceDyadicSamples.samples x) t

theorem ae_localBound (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, LocalBound (BrownianEntranceDyadicSamples.samples x) := by
  let := law_isProbability T hT
  exact FourthMomentDyadicModulus.ae_localBound (law T hT)
    (fun n k x ↦ BrownianEntranceDyadicSamples.samples x n k) measurable_sample
    (momentCoefficient T) (momentCoefficient_nonneg T) (fourth_dyadic_increment_bound T hT)

theorem ae_continuous_process (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, Continuous (fun t ↦ process t x) := by
  filter_upwards [ae_localBound T hT,ae_samples_compatible T hT] with x hb hc
  exact continuous_extension hc hb

theorem ae_samples_tendsto_process (T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0) :
    ∀ᵐ x ∂law T hT, Tendsto
      (fun n ↦ BrownianEntranceDyadicSamples.samples x n (index n t)) atTop (𝓝 (process t x)) := by
  filter_upwards [ae_localBound T hT,ae_samples_compatible T hT] with x hb hc
  exact samples_tendsto_extension hc hb t

theorem aemeasurable_process (T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0) :
    AEMeasurable (process t) (law T hT) := by
  exact aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n ↦ (measurable_sample n (index n t)).aemeasurable) (ae_samples_tendsto_process T hT t)

theorem ae_all_dyadic_process_eq (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ n k, process (coordinate n k) x =
      BrownianEntranceDyadicSamples.samples x n k := by
  filter_upwards [ae_localBound T hT,ae_samples_compatible T hT] with x hb hc
  exact extension_dyadic hc hb

theorem ae_process_initial_zero (T : ℝ≥0) (hT : 0 < T) : ∀ᵐ x ∂law T hT, process 0 x = 0 := by
  filter_upwards [ae_all_dyadic_process_eq T hT,ae_samples_initial_zero T hT] with x he hz
  simpa only [coordinate,Nat.cast_zero,zero_div] using (he 0 0).trans (hz 0)

/-- The right endpoint and the entire stopped portion are genuinely zero,
proved from the clamped samples and their geometric neighbor bound. -/
theorem ae_all_process_terminal_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ t, T ≤ t → process t x = 0 := by
  filter_upwards [ae_localBound T hT,ae_samples_compatible T hT,ae_samples_terminal_zero T hT]
    with x hb hc hz
  intro t ht
  obtain ⟨M,hM⟩ := exists_nat_gt (t : ℝ)
  obtain ⟨C,hC,hbound⟩ := hb M
  have hnorm (n : ℕ) : ‖BrownianEntranceDyadicSamples.samples x n (index n t)‖ ≤ C*ratio^n := by
    have hceil : t ≤ coordinate n (index n t+1) := by
      have he : (t : ℝ) ≤ (coordinate n (index n t+1) : ℝ) := by
        rw [coordinate_real,Nat.cast_add,Nat.cast_one]
        exact (le_div_iff₀ (by positivity : 0 < (2 : ℝ)^n)).mpr
          (scaled_lt_index_add_one n t).le
      exact_mod_cast he
    have hzero := hz n (index n t+1) (ht.trans hceil)
    have hn := hbound n (index n t) (index_lt_window hM n)
    simpa only [hzero,zero_sub,norm_neg] using hn
  have hnlim : Tendsto (fun n ↦ ‖BrownianEntranceDyadicSamples.samples x n (index n t)‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ norm_nonneg _) hnorm
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one ratio_nonneg ratio_lt_one).const_mul C
  have hzero : Tendsto (fun n ↦ BrownianEntranceDyadicSamples.samples x n (index n t))
      atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnlim
  exact tendsto_nhds_unique (samples_tendsto_extension hc hb t) hzero

theorem ae_all_clamped_process_eq (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ n k, process (clampedTime T n k) x =
      BrownianEntranceDyadicSamples.samples x n k := by
  filter_upwards [ae_all_dyadic_process_eq T hT,ae_all_process_terminal_zero T hT,
    ae_samples_terminal_zero T hT] with x he hp hz
  intro n k
  rcases le_total (coordinate n k) T with hle | hge
  · simpa only [clampedTime,min_eq_left hle] using he n k
  · rw [clampedTime,min_eq_right hge,hp T le_rfl,hz n k hge]

theorem ae_all_sampling_process_eq (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ i, process (samplingTimes T i) x = x i := by
  filter_upwards [ae_all_clamped_process_eq T hT] with x hx
  intro i
  simpa only [samplingTimes,BrownianEntranceDyadicSamples.samples,Nat.pair_unpair] using
    hx (Nat.unpair i).1 (Nat.unpair i).2

def sampledPath (x : ℕ → ℝ) : Path :=
  ContinuousMap.mkD (fun t ↦ process t x) (0 : C(ℝ≥0,ℝ))

theorem ae_all_sampledPath_eval (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ t, sampledPath x t = process t x := by
  filter_upwards [ae_continuous_process T hT] with x hx
  intro t
  exact ContinuousMap.mkD_apply_of_continuous hx

theorem aemeasurable_sampledPath (T : ℝ≥0) (hT : 0 < T) :
    AEMeasurable sampledPath (law T hT) := by
  apply rationalEval_measurableEmbedding.aemeasurable_comp_iff.mp
  have hm : AEMeasurable (fun x (q : BrownianGaussianSkeleton.RationalTime) ↦
      process (BrownianGaussianSkeleton.rationalTimeReal q) x) (law T hT) :=
    aemeasurable_pi_lambda _ (fun q ↦ aemeasurable_process T hT _)
  apply hm.congr
  filter_upwards [ae_all_sampledPath_eval T hT] with x hx
  exact funext (fun q ↦ (hx (BrownianGaussianSkeleton.rationalTimeReal q)).symm)

def measurablePath (T : ℝ≥0) (hT : 0 < T) : (ℕ → ℝ) → Path :=
  (aemeasurable_sampledPath T hT).mk sampledPath

theorem measurable_measurablePath (T : ℝ≥0) (hT : 0 < T) : Measurable (measurablePath T hT) :=
  (aemeasurable_sampledPath T hT).measurable_mk

theorem ae_all_measurablePath_eval (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ t, measurablePath T hT x t = process t x := by
  filter_upwards [(aemeasurable_sampledPath T hT).ae_eq_mk,ae_all_sampledPath_eval T hT] with x hx he
  intro t
  exact (congrArg (fun f : Path ↦ f t) hx).symm.trans (he t)

def pathLaw (T : ℝ≥0) (hT : 0 < T) : Measure Path :=
  (law T hT).map (measurablePath T hT)

theorem pathLaw_isProbability (T : ℝ≥0) (hT : 0 < T) : IsProbabilityMeasure (pathLaw T hT) := by
  let := law_isProbability T hT
  exact Measure.isProbabilityMeasure_map (measurable_measurablePath T hT).aemeasurable

theorem pathLaw_eq_map_sampledPath (T : ℝ≥0) (hT : 0 < T) :
    pathLaw T hT = (law T hT).map sampledPath :=
  Measure.map_congr (aemeasurable_sampledPath T hT).ae_eq_mk.symm

def pathSampling (T : ℝ≥0) (f : Path) : ℕ → ℝ := fun i ↦ f (samplingTimes T i)

theorem measurable_pathSampling (T : ℝ≥0) : Measurable (pathSampling T) :=
  measurable_pi_lambda _ (fun _i ↦ (continuous_eval _).measurable)

/-- The genuine continuous path law realizes the complete constructed
countable entrance law exactly. -/
theorem pathLaw_sampling_eq_source (T : ℝ≥0) (hT : 0 < T) :
    (pathLaw T hT).map (pathSampling T) = law T hT := by
  rw [pathLaw,Measure.map_map (measurable_pathSampling T) (measurable_measurablePath T hT)]
  have he : (pathSampling T ∘ measurablePath T hT) =ᵐ[law T hT] id := by
    filter_upwards [ae_all_measurablePath_eval T hT,ae_all_sampling_process_eq T hT] with x hx hs
    exact funext (fun i ↦ (hx (samplingTimes T i)).trans (hs i))
  rw [Measure.map_congr he,Measure.map_id]

theorem pathLaw_sampling_finite (T : ℝ≥0) (hT : 0 < T) (J : Finset ℕ) :
    (pathLaw T hT).map (fun f ↦ J.restrict (pathSampling T f)) =
      BrownianEntranceCountableLaw.sampleLaw T (samplingTimes T) J := by
  change (pathLaw T hT).map ((J.restrict (π := fun _ : ℕ ↦ ℝ)) ∘ pathSampling T) = _
  rw [← Measure.map_map (Finset.measurable_restrict J) (measurable_pathSampling T),
    pathLaw_sampling_eq_source]
  exact BrownianEntranceCountableLaw.law_projectiveLimit T hT (samplingTimes T) J

theorem ae_pathLaw_initial_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw T hT, f 0 = 0 := by
  unfold pathLaw
  apply (ae_map_iff (measurable_measurablePath T hT).aemeasurable
    (measurableSet_eq_fun (continuous_eval 0).measurable measurable_const)).mpr
  filter_upwards [ae_all_measurablePath_eval T hT,ae_process_initial_zero T hT] with x he hz
  exact (he 0).trans hz

theorem measurableSet_stopped_zero (T : ℝ≥0) :
    MeasurableSet {f : Path | ∀ t, T ≤ t → f t = 0} := by
  have hc (t : ℝ≥0) : IsClosed {f : Path | T ≤ t → f t = 0} := by
    by_cases ht : T ≤ t
    · simpa only [ht,true_implies] using isClosed_eq (continuous_eval t) continuous_const
    · simp only [ht,false_implies,Set.ofPred_true]
      exact isClosed_univ
  simpa only [Set.ofPred_forall] using (isClosed_iInter hc).measurableSet

theorem ae_pathLaw_stopped_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw T hT, ∀ t, T ≤ t → f t = 0 := by
  unfold pathLaw
  apply (ae_map_iff (measurable_measurablePath T hT).aemeasurable (measurableSet_stopped_zero T)).mpr
  filter_upwards [ae_all_measurablePath_eval T hT,ae_all_process_terminal_zero T hT] with x he hz
  intro t ht
  exact (he t).trans (hz t ht)

theorem ae_pathLaw_terminal_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw T hT, f T = 0 :=
  (ae_pathLaw_stopped_zero T hT).mono (fun _ hf ↦ hf T le_rfl)

end PerronWright.BrownianEntranceContinuousRealization
