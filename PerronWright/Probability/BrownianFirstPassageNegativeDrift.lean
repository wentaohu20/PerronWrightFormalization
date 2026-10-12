import PerronWright.Probability.BrownianFirstPassageBridgeLaw
import PerronWright.Probability.BrownianSublinearGrowth
import PerronWright.Probability.BrownianFullHorizonDrift

/-! # Finite actual first passage under negative linear Brownian drift

The full linear path, not its stopped approximation, is a genuine
continuous-path operation. The constructed Gaussian process has already
proved sublinear growth on the whole time axis. This implies that every
negative linear drift tends to minus infinity, and hence the literal
first passage time is finite and hits its level. No strong Markov,
first-passage density, or Palm identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFirstPassageNegativeDrift

open BrownianPathLaw ContinuousPathFirstPassage BrownianGaussianSkeleton
open BrownianContinuousModification BrownianSublinearGrowth

def linearPath (u : ℝ) (f : Path) : Path :=
  ⟨fun t ↦ f t+u*(t : ℝ),(continuous_path f).add (NNReal.continuous_coe.const_mul u)⟩

theorem linearPath_eval (u : ℝ) (f : Path) (t : ℝ≥0) :
    linearPath u f t = f t+u*(t : ℝ) := rfl

theorem continuous_linearPath (u : ℝ) : Continuous (linearPath u) := by
  let g : C(ℝ≥0,ℝ) := ⟨fun t ↦ u*(t : ℝ),NNReal.continuous_coe.const_mul u⟩
  change Continuous (fun f : C(ℝ≥0,ℝ) ↦ f+g)
  exact continuous_id.add continuous_const

theorem measurable_linearPath (u : ℝ) : Measurable (linearPath u) :=
  (continuous_linearPath u).measurable

theorem linear_tendsto_atBot_of_sublinear {f : ℝ≥0 → ℝ}
    (hf : Tendsto (fun t : ℝ≥0 ↦ f t/(t : ℝ)) atTop (𝓝 0))
    (u : ℝ) (hu : u < 0) :
    Tendsto (fun t : ℝ≥0 ↦ f t+u*(t : ℝ)) atTop atBot := by
  have hr := hf.eventually (Iio_mem_nhds (show (0 : ℝ) < -u/2 by linarith))
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [hr, BrownianFullHorizonDrift.tendsto_nnreal_coe_atTop.eventually
    (eventually_ge_atTop (2*b/u)),eventually_ge_atTop (1 : ℝ≥0)] with t hratio hb ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht
  have h := (div_lt_iff₀ htpos).mp hratio
  have hbound : (u/2)*(t : ℝ) ≤ b := calc
    _ ≤ (u/2)*(2*b/u) := mul_le_mul_of_nonpos_left hb (by linarith)
    _ = b := by field_simp [hu.ne]
  nlinarith

theorem firstPassage_ne_top_of_tendsto_atBot (level : ℝ) (f : Path)
    (hf : Tendsto (fun t ↦ f t) atTop atBot) : firstPassage level f ≠ ⊤ := by
  obtain ⟨t,ht⟩ := (hf.eventually (eventually_le_atBot level)).exists
  intro hn
  exact (not_le_of_gt ((firstPassage_eq_top_iff level f).mp hn t)) ht

/-- The actual Gaussian source has finite first passages for all negative
linear parameters and all levels on the same proved full-measure set. -/
theorem ae_all_negative_parameter_source_finite :
    ∀ᵐ x ∂rationalLaw, ∀ u : ℝ, u < 0 → ∀ level : ℝ,
      firstPassage level (linearPath u (measurablePath x)) ≠ ⊤ := by
  filter_upwards [ae_sublinear_process,ae_all_measurablePath_eval] with x hx hmatch
  intro u hu level
  apply firstPassage_ne_top_of_tendsto_atBot
  have hs : Tendsto (fun t : ℝ≥0 ↦ measurablePath x t/(t : ℝ)) atTop (𝓝 0) := by
    simpa only [hmatch] using hx
  exact linear_tendsto_atBot_of_sublinear hs u hu

/-- Finite literal first passage under the genuine full-horizon Brownian
path probability law; its growth hypothesis has been discharged. -/
theorem ae_firstPassage_ne_top (level : ℝ) (u : ℝ) (hu : u < 0) :
    ∀ᵐ f : Path ∂pathLaw, firstPassage level (linearPath u f) ≠ ⊤ := by
  have hm : Measurable (fun f : Path ↦ firstPassage level (linearPath u f)) :=
    (measurable_firstPassage level).comp (measurable_linearPath u)
  have hs : MeasurableSet {f : Path | firstPassage level (linearPath u f) ≠ ⊤} := by
    exact (hm (measurableSet_singleton ⊤)).compl
  rw [pathLaw]
  exact (ae_map_iff measurable_measurablePath.aemeasurable hs).mpr
    (ae_all_negative_parameter_source_finite.mono (fun _ hx ↦ hx u hu level))

theorem ae_firstPassage_lt_top (level : ℝ) (u : ℝ) (hu : u < 0) :
    ∀ᵐ f : Path ∂pathLaw, firstPassage level (linearPath u f) < ⊤ :=
  (ae_firstPassage_ne_top level u hu).mono (fun _ hx ↦ lt_top_iff_ne_top.mpr hx)

theorem ae_firstPassage_pos (level : ℝ) (hlevel : level < 0) (u : ℝ) :
    ∀ᵐ f : Path ∂pathLaw, 0 < firstPassage level (linearPath u f) := by
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  by_contra h
  have hm := (firstPassage_le_iff level (linearPath u f) 0).mp (le_of_not_gt h)
  obtain ⟨t,ht,he⟩ := hm
  have ht0 : t = 0 := le_antisymm ht zero_le
  subst t
  have hh : (0 : ℝ) ≤ level := by
    simpa only [linearPath_eval,NNReal.coe_zero,mul_zero,add_zero,hf] using he
  exact (not_le_of_gt hlevel) hh

theorem ae_firstPassage_exact_level (level : ℝ) (hlevel : level < 0)
    (u : ℝ) (hu : u < 0) :
    ∀ᵐ f : Path ∂pathLaw,
      linearPath u f (firstPassage level (linearPath u f)).toNNReal = level := by
  filter_upwards [ae_firstPassage_ne_top level u hu,
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hfin hf
  apply firstPassage_exact_level level _ _ hfin
  simpa only [linearPath_eval,NNReal.coe_zero,mul_zero,add_zero,hf] using hlevel

theorem survival_linearPath_iff_stoppedDrift (level : ℝ) (T : ℝ≥0) (u : ℝ) (f : Path) :
    linearPath u f ∈ survival level T ↔
      BrownianEndpointDriftTilt.driftPath T u f ∈ survival level T := by
  rw [mem_survival_iff,mem_survival_iff]
  constructor <;> intro h t ht
  · have ht' : (t : ℝ) ≤ T := by exact_mod_cast ht
    simpa only [BrownianEndpointDriftTilt.driftPath_eval,min_eq_left ht',linearPath_eval] using h t ht
  · have ht' : (t : ℝ) ≤ T := by exact_mod_cast ht
    simpa only [BrownianEndpointDriftTilt.driftPath_eval,min_eq_left ht',linearPath_eval] using h t ht

/-- Exact finite-horizon first-passage probability for the actual full
linear drift, including its endpoint, in terms of the actual pinned law. -/
theorem firstPassage_survival_endpoint_probability (level : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage level (linearPath u f) ∧
      linearPath u f T ∈ B} =
      ∫⁻ z in B, BrownianFirstPassageBridgeLaw.pinnedLaw T
        (BrownianFirstPassageBridgeLaw.bridgeConstraint level T z)
        ∂gaussianReal (u*(T : ℝ)) T := by
  have he : {f : Path | (T : ℝ≥0∞) < firstPassage level (linearPath u f) ∧ linearPath u f T ∈ B} =
      {f : Path | (T : ℝ≥0∞) < firstPassage level (BrownianEndpointDriftTilt.driftPath T u f) ∧
        f T+u*(T : ℝ) ∈ B} := by
    ext f
    change (_ ∧ linearPath u f T ∈ B) ↔ (_ ∧ f T+u*(T : ℝ) ∈ B)
    rw [linearPath_eval,← mem_survival_iff_firstPassage,← mem_survival_iff_firstPassage,
      survival_linearPath_iff_stoppedDrift]
  rw [he]
  exact BrownianFirstPassageBridgeLaw.drift_firstPassage_survival_endpoint_probability
    level T hT u hB

end PerronWright.BrownianFirstPassageNegativeDrift
