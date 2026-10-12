import PerronWright.Probability.BrownianMinimumSplitCandidate
import PerronWright.Probability.BrownianFreeEntranceUnitMass
import PerronWright.Probability.BrownianSurvivalEntranceScaling
import PerronWright.Probability.BrownianMinimumSplitWindowNonnegativeLimit

/-! # Genuine probability normalization of the minimum-split candidate

The constant-test limit of actual Brownian minimum windows is one.
The proved entrance mass, actual stopped-past time marginal and genuine
survival domination exchange that limit through the entire depth/time
integral. This proves the explicit candidate has mass one independently
of any full minimum-split law identification.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumSplitCandidateProbability

open BrownianPathLaw ContinuousPathFirstPassage BrownianMinimumSplitCandidate
open BrownianFirstPassageEndpointGeometry BrownianMinimumWindowSurvivalBounds
open BrownianFirstPassagePastTimeMarginal BrownianFirstPassageMinimumWindowPastFutureLaw
open BrownianMinimumFutureEntranceSource BrownianKilledFreeEntranceTests
open BrownianKilledFiniteDimensionalOrderedTimes BrownianSurvivalEntranceScaling

private theorem actual_survival_mass_tendsto (r : ℝ≥0) (hr : 0 < r) :
    Tendsto (fun δ : ℝ ↦ pathLaw (survival (-δ) r)/ENNReal.ofReal δ) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt (r : ℝ)))) := by
  let times : Fin 2 → ℝ≥0 := fun i ↦ (i.val : ℝ≥0)
  have hstrict : StrictMono times := fun i j hij ↦ by
    change (i.val : ℝ≥0) < (j.val : ℝ≥0)
    exact_mod_cast hij
  have hzero : times 0 = 0 := by simp [times]
  have hlast : times (Fin.last 1) = 1 := by simp [times]
  have ht := actual_relative_ordered_test_tendsto 0 times hstrict hzero r hr
    (BoundedContinuousFunction.const _ (1 : ℝ)) (fun _ ↦ zero_le_one)
  simp only [BoundedContinuousFunction.const_apply',ENNReal.ofReal_one,lintegral_const,
    Measure.restrict_apply_univ,mul_one,hlast] at ht
  rw [BrownianFreeEntranceUnitMass.freeEntranceLaw_unit_mass 0 times hstrict hzero hlast] at ht
  have hinv : ENNReal.ofReal (1/Real.sqrt (r : ℝ)) =
      (ENNReal.ofReal (Real.sqrt (r : ℝ)))⁻¹ := by
    rw [one_div]
    exact ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hr)
  simpa only [mul_one,one_mul,entranceCoefficient,hinv,mul_comm] using ht

private def survivalMass (T : ℝ≥0) (δ s : ℝ) : ℝ≥0∞ :=
  pathLaw (survival (-δ) (remainingTime T s))

private theorem measurable_survivalMass (T : ℝ≥0) (δ : ℝ) : Measurable (survivalMass T δ) := by
  have hm := (measurable_const : Measurable (fun _ : ℝ × Path ↦ (1 : ℝ≥0∞))).indicator
    (BrownianFirstPassageMinimumWindowGeometry.measurableSet_futureSurvival δ T)
  have h := hm.lintegral_prod_right' (ν := pathLaw)
  convert h using 1
  funext s
  have he : (fun g : Path ↦ (BrownianFirstPassageMinimumWindowGeometry.futureSurvival δ T).indicator
      (fun _ ↦ (1 : ℝ≥0∞)) (s,g)) =
      (survival (-δ) (remainingTime T s)).indicator (fun _ ↦ (1 : ℝ≥0∞)) := rfl
  rw [he,lintegral_indicator (measurableSet_survival (-δ) (remainingTime T s)),
    lintegral_const,Measure.restrict_apply_univ,one_mul]
  rfl

private def passageMass (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))

private theorem measurable_passageMass : Measurable passageMass := by
  unfold passageMass
  fun_prop

private def limitKernel (T : ℝ≥0) (s : ℝ) : ℝ≥0∞ :=
  passageMass s*(ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-s)))

private theorem time_mass_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun δ : ℝ ↦ ∫⁻ s in Ioo (0 : ℝ) (T : ℝ),
      passageMass s*(survivalMass T δ s/ENNReal.ofReal δ)) (𝓝[>] 0)
      (𝓝 (∫⁻ s in Ioo (0 : ℝ) (T : ℝ), limitKernel T s)) := by
  have hm (δ : ℝ) : Measurable (fun s ↦ passageMass s*(survivalMass T δ s/ENNReal.ofReal δ)) :=
    measurable_passageMass.mul ((measurable_survivalMass T δ).div_const _)
  have hb : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (T : ℝ)),
      passageMass s*(survivalMass T δ s/ENNReal.ofReal δ) ≤
        ENNReal.ofReal (majorantCoefficient*timeMajorant T s) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [passageMass,← passage_level_mass s hs.1]
    exact normalized_level_survival_mass_bound T s hs δ hδ
  have hfin : (∫⁻ s in Ioo (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (majorantCoefficient*timeMajorant T s)) ≠ ⊤ := by
    simp_rw [ENNReal.ofReal_mul majorantCoefficient_nonneg]
    rw [lintegral_const_mul _ (measurable_timeMajorant T).ennreal_ofReal]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_timeMajorant_ne_top T hT)
  apply tendsto_lintegral_filter_of_dominated_convergence
    (fun s ↦ ENNReal.ofReal (majorantCoefficient*timeMajorant T s))
    (Eventually.of_forall hm) hb hfin
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hr : 0 < remainingTime T s := Real.toNNReal_pos.mpr (sub_pos.mpr hs.2)
  have hc : (remainingTime T s : ℝ) = (T : ℝ)-s := Real.coe_toNNReal _ (sub_pos.mpr hs.2).le
  have ht := ENNReal.Tendsto.const_mul (a := passageMass s)
    (actual_survival_mass_tendsto (remainingTime T s) hr) (Or.inr ENNReal.ofReal_ne_top)
  simpa only [survivalMass,limitKernel,hc] using ht

private theorem window_mass_eq_time (T : ℝ≥0) (δ : ℝ) :
    ((∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
      survivalMass T δ (p.1 : ℝ) ∂passagePastLaw (-a))/ENNReal.ofReal δ) =
      ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), passageMass s*(survivalMass T δ s/ENNReal.ofReal δ) := by
  rw [lintegral_level_past_time_density T (fun p : ℝ × ℝ ↦ survivalMass T δ p.2)
    ((measurable_survivalMass T δ).comp measurable_snd)]
  change ((∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
    BrownianFirstPassageDensityGeometry.density a s*survivalMass T δ s)/ENNReal.ofReal δ) = _
  have he : (fun s : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*survivalMass T δ s) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) (T : ℝ))] fun s ↦ passageMass s*survivalMass T δ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hd : Measurable (fun a : ℝ ↦ BrownianFirstPassageDensityGeometry.density a s) :=
      BrownianHeatResolvent.measurable_joint_passageDensity.comp
        (measurable_id.prodMk measurable_const)
    rw [lintegral_mul_const'' _ hd.aemeasurable,passage_level_mass s hs.1]
    rfl
  have hm : Measurable (fun s : ℝ ↦ passageMass s*survivalMass T δ s) :=
    measurable_passageMass.mul (measurable_survivalMass T δ)
  rw [lintegral_congr_ae he,div_eq_mul_inv,← lintegral_mul_const _ hm]
  exact lintegral_congr (fun s ↦ mul_assoc _ _ _)

private theorem candidate_mass_eq_time (T : ℝ≥0) :
    candidateLaw T univ = ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), limitKernel T s := by
  have hc := lintegral_candidateLaw T (fun _ ↦ (1 : ℝ≥0∞)) measurable_const
  simp only [lintegral_const,measure_univ,one_mul,mul_one] at hc
  rw [lintegral_level_past_time_density T (fun p : ℝ × ℝ ↦
      ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-p.2)))
    (by fun_prop)] at hc
  calc
    _ = ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-s))) := hc
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hd : Measurable (fun a : ℝ ↦ BrownianFirstPassageDensityGeometry.density a s) :=
        BrownianHeatResolvent.measurable_joint_passageDensity.comp
          (measurable_id.prodMk measurable_const)
      rw [lintegral_mul_const'' _ hd.aemeasurable,passage_level_mass s hs.1]
      rfl

theorem candidateLaw_univ (T : ℝ≥0) (hT : 0 < T) : candidateLaw T univ = 1 := by
  have ht := BrownianMinimumSplitWindowNonnegativeLimit.actual_split_past_future_product_limit
    T hT (BoundedContinuousFunction.const _ (1 : ℝ)) (fun _ ↦ zero_le_one)
  simp only [BoundedContinuousFunction.const_apply',ENNReal.ofReal_one,lintegral_const,
    Measure.restrict_apply_univ,measure_univ,one_mul] at ht
  have hactual := ht.congr (fun δ ↦ window_mass_eq_time T δ)
  have he := tendsto_nhds_unique hactual (time_mass_tendsto T hT)
  exact (candidate_mass_eq_time T).trans he.symm

theorem candidateLaw_isProbability (T : ℝ≥0) (hT : 0 < T) :
    IsProbabilityMeasure (candidateLaw T) := ⟨candidateLaw_univ T hT⟩

end PerronWright.BrownianMinimumSplitCandidateProbability
