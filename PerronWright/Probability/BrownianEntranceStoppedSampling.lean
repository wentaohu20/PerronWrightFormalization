import PerronWright.Probability.BrownianEntranceContinuousRealization

/-! # Literal stopped paths are determined by clamped dyadic samples

The sampling times are those of the constructed entrance law. Their
density is proved from the actual dyadic floor inequalities. No path-law
identification, arbitrary-time density continuity, or regularity premise
is needed here: elements of `Path` are already continuous functions.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceStoppedSampling

open BrownianPathLaw BrownianEntranceDyadicSamples
open BrownianEntranceContinuousRealization DyadicFloorGeometry

def stoppedPaths (T : ℝ≥0) : Set Path := {f | ∀ t, T ≤ t → f t = f T}

theorem isClosed_stoppedPaths (T : ℝ≥0) : IsClosed (stoppedPaths T) := by
  have hc (t : ℝ≥0) : IsClosed {f : Path | T ≤ t → f t = f T} := by
    by_cases ht : T ≤ t
    · simpa only [ht,true_implies] using isClosed_eq (continuous_eval t) (continuous_eval T)
    · simp only [ht,false_implies,Set.ofPred_true]
      exact isClosed_univ
  simpa only [stoppedPaths,Set.ofPred_forall] using isClosed_iInter hc

theorem measurableSet_stoppedPaths (T : ℝ≥0) : MeasurableSet (stoppedPaths T) :=
  (isClosed_stoppedPaths T).measurableSet

theorem coordinate_floor_le (n : ℕ) (t : ℝ≥0) : coordinate n (index n t) ≤ t := by
  have hr : (coordinate n (index n t) : ℝ) ≤ t := by
    rw [coordinate_real]
    exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^n)).mpr (index_le_scaled n t)
  exact_mod_cast hr

theorem coordinate_floor_error (n : ℕ) (t : ℝ≥0) :
    ‖(coordinate n (index n t) : ℝ) - t‖ ≤ 1/(2 : ℝ)^n := by
  have hp : 0 < (2 : ℝ)^n := by positivity
  have hlo : (coordinate n (index n t) : ℝ) ≤ t := by
    exact_mod_cast coordinate_floor_le n t
  have hhi : (t : ℝ) < (coordinate n (index n t) : ℝ) + 1/(2 : ℝ)^n := by
    rw [coordinate_real,← add_div]
    exact (lt_div_iff₀ hp).mpr (scaled_lt_index_add_one n t)
  rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith

theorem coordinate_floor_tendsto (t : ℝ≥0) :
    Tendsto (fun n ↦ coordinate n (index n t)) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ coordinate_floor_error n t)
  simpa only [div_pow,one_pow] using
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)

theorem clamped_floor_tendsto (T t : ℝ≥0) :
    Tendsto (fun n ↦ clampedTime T n (index n t)) atTop (𝓝 (min t T)) :=
  (coordinate_floor_tendsto t).min tendsto_const_nhds

theorem continuous_pathSampling (T : ℝ≥0) : Continuous (pathSampling T) :=
  continuous_pi (fun _ ↦ continuous_eval _)

theorem sampled_paths_eq_at_clamped_time (T : ℝ≥0) {f g : Path}
    (h : pathSampling T f = pathSampling T g) (t : ℝ≥0) : f (min t T) = g (min t T) := by
  have hs (n : ℕ) : f (clampedTime T n (index n t)) = g (clampedTime T n (index n t)) := by
    have hn := congrFun h (Nat.pair n (index n t))
    simpa only [pathSampling,samplingTimes_pair] using hn
  have hf := (continuous_path f).continuousAt.tendsto.comp (clamped_floor_tendsto T t)
  have hg := (continuous_path g).continuousAt.tendsto.comp (clamped_floor_tendsto T t)
  have he : (fun n ↦ f (clampedTime T n (index n t))) =
      (fun n ↦ g (clampedTime T n (index n t))) := funext hs
  change Tendsto (fun n ↦ f (clampedTime T n (index n t))) atTop (𝓝 (f (min t T))) at hf
  rw [he] at hf
  exact tendsto_nhds_unique hf hg

theorem pathSampling_injective_on_stopped (T : ℝ≥0) :
    Set.InjOn (pathSampling T) (stoppedPaths T) := by
  intro f hf g hg h
  apply DFunLike.ext
  intro t
  have hc := sampled_paths_eq_at_clamped_time T h t
  rcases le_total t T with ht | ht
  · simpa only [min_eq_left ht] using hc
  · simpa only [min_eq_right ht,hf t ht,hg t ht] using hc

theorem stoppedSampling_measurableEmbedding (T : ℝ≥0) :
    MeasurableEmbedding ((stoppedPaths T).domRestrict (pathSampling T)) :=
  (continuous_pathSampling T).continuousOn.measurableEmbedding
    (measurableSet_stoppedPaths T) (pathSampling_injective_on_stopped T)

theorem ae_pathLaw_stopped (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw T hT, f ∈ stoppedPaths T := by
  filter_upwards [ae_pathLaw_stopped_zero T hT] with f hf
  intro t ht
  rw [hf t ht,hf T le_rfl]

end PerronWright.BrownianEntranceStoppedSampling
