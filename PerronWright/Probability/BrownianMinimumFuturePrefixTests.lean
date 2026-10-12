import PerronWright.Probability.BrownianMinimumFutureEntranceSource
import PerronWright.Probability.BrownianSurvivalEntranceScaling
import PerronWright.Probability.BrownianMinimumSplitWindowNonnegativeLimit
import PerronWright.Probability.BrownianFirstPassagePastTimeMarginal
import PerronWright.Probability.BrownianFreeEntranceUnitMass
import PerronWright.Probability.ContinuousTimeCutoff
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Genuine finite prefix tests after the actual unit minimum

First-passage window products and the proved surviving Brownian entrance
limit identify the finite prefix of the literal minimum future. A time
cutoff makes the relative observation test globally bounded continuous;
the actual inverse-square-root time domination removes that cutoff.
No meander or weak-limit distribution is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFuturePrefixTests

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianPathIndependentIncrements BrownianMinimumFutureEntranceSource
open BrownianFirstPassageEndpointGeometry BrownianMinimumWindowSurvivalBounds
open BrownianFirstPassagePastTimeMarginal BrownianFirstPassageMinimumWindowPastFutureLaw
open BrownianKilledFreeEntranceTests BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalOrderedDensity
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianSurvivalEntranceScaling
open ContinuousPathMinimumSplitBandAverage

private def scale (ε s : ℝ≥0) : ℝ≥0 := max ε (1-s)

private theorem continuous_scale (ε : ℝ≥0) : Continuous (scale ε) :=
  continuous_const.max (continuous_const.sub continuous_id)

private def relativeTuple (n : ℕ) (times : Fin (n+2) → ℝ≥0) (ε : ℝ≥0)
    (q : ℝ≥0 × Path) : FreeVector (n+1) :=
  fun i ↦ q.2 (scale ε q.1*times i.succ)/Real.sqrt (scale ε q.1 : ℝ)

private theorem continuous_relativeTuple (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (ε : ℝ≥0) (hε : 0 < ε) : Continuous (relativeTuple n times ε) := by
  apply continuous_pi
  intro i
  have hc : Continuous (fun q : ℝ≥0 × Path ↦ scale ε q.1) :=
    (continuous_scale ε).comp continuous_fst
  have hs := Real.continuous_sqrt.comp (NNReal.continuous_coe.comp hc)
  exact (continuous_joint_eval.comp
    (continuous_snd.prodMk (hc.mul_const _))).div hs
      (fun q ↦ ne_of_gt (Real.sqrt_pos.mpr (hε.trans_le (le_max_left _ _))))

private def rawTest (n : ℕ) (times : Fin (n+2) → ℝ≥0) (ε : ℝ≥0) (hε : 0 < ε)
    (κ : ℝ≥0 →ᵇ ℝ) (G : FreeVector (n+1) →ᵇ ℝ) : (ℝ≥0 × Path) →ᵇ ℝ :=
  (κ.compContinuous ⟨Prod.fst,continuous_fst⟩)*
    (G.compContinuous ⟨relativeTuple n times ε,continuous_relativeTuple n times ε hε⟩)

private def splitTest (n : ℕ) (times : Fin (n+2) → ℝ≥0) (ε : ℝ≥0) (hε : 0 < ε)
    (κ : ℝ≥0 →ᵇ ℝ) (G : FreeVector (n+1) →ᵇ ℝ) :
    ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ :=
  (rawTest n times ε hε κ G).compContinuous
    ⟨fun p ↦ (p.1.1,p.2.2),continuous_fst.fst.prodMk continuous_snd.snd⟩

private def rawKernel (n : ℕ) (times : Fin (n+2) → ℝ≥0) (ε : ℝ≥0) (hε : 0 < ε)
    (κ : ℝ≥0 →ᵇ ℝ) (G : FreeVector (n+1) →ᵇ ℝ) (δ s : ℝ) : ℝ≥0∞ :=
  ∫⁻ g in survival (-δ) (remainingTime 1 s),
    ENNReal.ofReal (rawTest n times ε hε κ G (Real.toNNReal s,g)) ∂pathLaw

private theorem measurable_rawKernel (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (ε : ℝ≥0) (hε : 0 < ε) (κ : ℝ≥0 →ᵇ ℝ) (G : FreeVector (n+1) →ᵇ ℝ)
    (δ : ℝ) : Measurable (rawKernel n times ε hε κ G δ) := by
  have hm : Measurable (fun q : ℝ × Path ↦
      ENNReal.ofReal (rawTest n times ε hε κ G (Real.toNNReal q.1,q.2))) :=
    ((rawTest n times ε hε κ G).continuous.measurable.comp
      (measurable_fst.real_toNNReal.prodMk measurable_snd)).ennreal_ofReal
  have hi := hm.indicator (BrownianFirstPassageMinimumWindowGeometry.measurableSet_futureSurvival δ 1)
  have h := hi.lintegral_prod_right' (ν := pathLaw)
  convert h using 1
  funext s
  unfold rawKernel
  rw [← lintegral_indicator (measurableSet_survival (-δ) (remainingTime 1 s))]
  rfl

private def timeWeight (κ : ℝ≥0 →ᵇ ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (κ (Real.toNNReal s))*
    ENNReal.ofReal ((1/Real.sqrt (2*Real.pi))*timeMajorant 1 s)

private theorem measurable_timeWeight (κ : ℝ≥0 →ᵇ ℝ) : Measurable (timeWeight κ) := by
  exact ((by fun_prop : Measurable (fun s : ℝ ↦ κ (Real.toNNReal s))).ennreal_ofReal).mul
    (((measurable_timeMajorant 1).const_mul _).ennreal_ofReal)

private theorem product_window_eq_time (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (ε : ℝ≥0) (hε : 0 < ε) (κ : ℝ≥0 →ᵇ ℝ) (G : FreeVector (n+1) →ᵇ ℝ) (δ : ℝ) :
    ((∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < 1},
      ∫⁻ g in survival (-δ) (remainingTime 1 (p.1 : ℝ)),
        ENNReal.ofReal (splitTest n times ε hε κ G (p,-a,g)) ∂pathLaw
          ∂passagePastLaw (-a))/ENNReal.ofReal δ) =
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
        (rawKernel n times ε hε κ G δ s/ENNReal.ofReal δ) := by
  have hraw (a : ℝ) (p : ℝ≥0 × Path) :
      (∫⁻ g in survival (-δ) (remainingTime 1 (p.1 : ℝ)),
        ENNReal.ofReal (splitTest n times ε hε κ G (p,-a,g)) ∂pathLaw) =
        rawKernel n times ε hε κ G δ (p.1 : ℝ) := by
    simp only [rawKernel,Real.toNNReal_coe,splitTest,
      BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk]
  simp_rw [hraw]
  rw [lintegral_level_past_time_density 1
    (fun p : ℝ × ℝ ↦ rawKernel n times ε hε κ G δ p.2)
    ((measurable_rawKernel n times ε hε κ G δ).comp measurable_snd)]
  change ((∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ a in Ioi (0 : ℝ),
    BrownianFirstPassageDensityGeometry.density a s*rawKernel n times ε hε κ G δ s)/
      ENNReal.ofReal δ) = _
  have he : (fun s : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*rawKernel n times ε hε κ G δ s) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)]
      fun s ↦ ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
        rawKernel n times ε hε κ G δ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hd : Measurable (fun a : ℝ ↦ BrownianFirstPassageDensityGeometry.density a s) :=
      BrownianHeatResolvent.measurable_joint_passageDensity.comp
        (measurable_id.prodMk measurable_const)
    rw [lintegral_mul_const'' _ hd.aemeasurable,passage_level_mass s hs.1]
  have hm : Measurable (fun s : ℝ ↦ ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
      rawKernel n times ε hε κ G δ s) :=
    (by fun_prop : Measurable (fun s : ℝ ↦ ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s)))).mul
      (measurable_rawKernel n times ε hε κ G δ)
  rw [lintegral_congr_ae he,div_eq_mul_inv,← lintegral_mul_const _ hm]
  apply lintegral_congr
  intro s
  simp only [div_eq_mul_inv,mul_assoc]

private theorem scale_eq_remaining (b s : ℝ≥0) (hs : s < b) :
    scale (1-b) s = 1-s :=
  max_eq_right (tsub_le_tsub_left hs.le 1)

private theorem remainingTime_one (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    remainingTime 1 s = 1-Real.toNNReal s := by
  apply NNReal.coe_injective
  have hsn : Real.toNNReal s ≤ (1 : ℝ≥0) := by
    exact_mod_cast (Real.coe_toNNReal s hs.1.le).trans_le hs.2.le
  rw [NNReal.coe_sub hsn,Real.coe_toNNReal s hs.1.le]
  exact Real.coe_toNNReal _ (by simpa only [NNReal.coe_one] using (sub_pos.mpr hs.2).le)

private theorem rawKernel_tendsto (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1)
    (b : ℝ≥0) (hb : b < 1) (κ : ℝ≥0 →ᵇ ℝ) (hκ : ∀ s, 0 ≤ κ s ∧ κ s ≤ 1)
    (hcut : ∀ s, b ≤ s → κ s = 0) (G : FreeVector (n+1) →ᵇ ℝ) (hG : ∀ v, 0 ≤ G v)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
      (rawKernel n times (1-b) (tsub_pos_iff_lt.mpr hb) κ G δ s/ENNReal.ofReal δ))
      (𝓝[>] 0) (𝓝 (timeWeight κ s*
        ∫⁻ v, ENNReal.ofReal (G v) ∂freeEntranceLaw n (orderedGaps (n+1) times))) := by
  let c := remainingTime 1 s
  have hc : 0 < c := Real.toNNReal_pos.mpr (by simpa only [NNReal.coe_one] using sub_pos.mpr hs.2)
  have hec : (c : ℝ) = 1-s := Real.coe_toNNReal _ (sub_pos.mpr hs.2).le
  by_cases hk : κ (Real.toNNReal s) = 0
  · have hkernel (δ : ℝ) : rawKernel n times (1-b) (tsub_pos_iff_lt.mpr hb) κ G δ s = 0 := by
      simp only [rawKernel,rawTest,BoundedContinuousFunction.mul_apply,
        BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,hk,
        zero_mul,ENNReal.ofReal_zero,lintegral_zero]
    simp only [hkernel,ENNReal.zero_div,mul_zero,timeWeight,hk,ENNReal.ofReal_zero,zero_mul]
    exact tendsto_const_nhds
  · have hsb : Real.toNNReal s < b := lt_of_not_ge (fun h ↦ hk (hcut _ h))
    have hscale : scale (1-b) (Real.toNNReal s) = c := by
      rw [scale_eq_remaining b _ hsb,← remainingTime_one s hs]
    let GG : FreeVector (n+1) →ᵇ ℝ :=
      (BoundedContinuousFunction.const _ (κ (Real.toNNReal s)))*G
    have hGG : ∀ v, 0 ≤ GG v := fun v ↦ mul_nonneg (hκ _).1 (hG v)
    have ht := actual_relative_ordered_test_tendsto n times hstrict hzero c hc GG hGG
    rw [hlast,mul_one] at ht
    have hsource (δ : ℝ) : rawKernel n times (1-b) (tsub_pos_iff_lt.mpr hb) κ G δ s =
        ∫⁻ f in survival (-δ) c, ENNReal.ofReal (GG (fun i : Fin (n+1) ↦
          f (c*times i.succ)/Real.sqrt (c : ℝ))) ∂pathLaw := by
      have htuple (f : Path) : relativeTuple n times (1-b) (Real.toNNReal s,f) =
          (fun i : Fin (n+1) ↦ f (c*times i.succ)/Real.sqrt (c : ℝ)) := by
        funext i
        change f (scale (1-b) (Real.toNNReal s)*times i.succ)/
          Real.sqrt (scale (1-b) (Real.toNNReal s) : ℝ) = _
        rw [hscale]
      simp only [rawKernel,rawTest,BoundedContinuousFunction.mul_apply,
        BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
        htuple,GG,BoundedContinuousFunction.const_apply']
      rfl
    have htarget : (∫⁻ v, ENNReal.ofReal (GG v) ∂freeEntranceLaw n (orderedGaps (n+1) times)) =
        ENNReal.ofReal (κ (Real.toNNReal s))*
          ∫⁻ v, ENNReal.ofReal (G v) ∂freeEntranceLaw n (orderedGaps (n+1) times) := by
      simp only [GG,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.const_apply',
        ENNReal.ofReal_mul (hκ _).1]
      exact lintegral_const_mul _ G.continuous.measurable.ennreal_ofReal
    have ht' := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))) ht
      (Or.inr ENNReal.ofReal_ne_top)
    simp only [← hsource,htarget] at ht'
    have hcoef : timeWeight κ s =
        ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
          ((ENNReal.ofReal (Real.sqrt (c : ℝ)))⁻¹*ENNReal.ofReal (κ (Real.toNNReal s))) := by
      have hre : (1/Real.sqrt (2*Real.pi))*timeMajorant 1 s =
          (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*(Real.sqrt (c : ℝ))⁻¹ := by
        unfold timeMajorant
        rw [hec]
        simp only [NNReal.coe_one]
        ring
      rw [timeWeight,hre,ENNReal.ofReal_mul (by positivity)]
      have hinv : ENNReal.ofReal ((Real.sqrt (c : ℝ))⁻¹) =
          (ENNReal.ofReal (Real.sqrt (c : ℝ)))⁻¹ :=
        ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hc)
      rw [hinv]
      ac_rfl
    simpa only [hcoef,mul_assoc] using ht'

private theorem rawKernel_time_tendsto (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1)
    (b : ℝ≥0) (hb : b < 1) (κ : ℝ≥0 →ᵇ ℝ) (hκ : ∀ s, 0 ≤ κ s ∧ κ s ≤ 1)
    (hcut : ∀ s, b ≤ s → κ s = 0) (G : FreeVector (n+1) →ᵇ ℝ) (hG : ∀ v, 0 ≤ G v) :
    Tendsto (fun δ : ℝ ↦ ∫⁻ s in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
        (rawKernel n times (1-b) (tsub_pos_iff_lt.mpr hb) κ G δ s/ENNReal.ofReal δ))
      (𝓝[>] 0) (𝓝 ((∫⁻ s in Ioo (0 : ℝ) 1, timeWeight κ s)*
        ∫⁻ v, ENNReal.ofReal (G v) ∂freeEntranceLaw n (orderedGaps (n+1) times))) := by
  let C : ℝ := ‖G‖*majorantCoefficient
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) majorantCoefficient_nonneg
  have hm (δ : ℝ) : Measurable (fun s : ℝ ↦
      ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
        (rawKernel n times (1-b) (tsub_pos_iff_lt.mpr hb) κ G δ s/ENNReal.ofReal δ)) :=
    (by fun_prop : Measurable (fun s : ℝ ↦ ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s)))).mul
      ((measurable_rawKernel n times (1-b) (tsub_pos_iff_lt.mpr hb) κ G δ).div_const _)
  have hbnd : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1),
      ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
        (rawKernel n times (1-b) (tsub_pos_iff_lt.mpr hb) κ G δ s/ENNReal.ofReal δ) ≤
          ENNReal.ofReal (C*timeMajorant 1 s) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have htest (g : Path) : ENNReal.ofReal
        (rawTest n times (1-b) (tsub_pos_iff_lt.mpr hb) κ G (Real.toNNReal s,g)) ≤
        ENNReal.ofReal ‖G‖ := by
      apply ENNReal.ofReal_le_ofReal
      change κ (Real.toNNReal s)*G (relativeTuple n times (1-b) (Real.toNNReal s,g)) ≤ ‖G‖
      exact (mul_le_mul_of_nonneg_right (hκ _).2 (hG _)).trans
        (by simpa only [one_mul,Real.norm_eq_abs] using
          (le_abs_self _).trans (G.norm_coe_le_norm _))
    have htestbound := normalized_survival_test_bound δ (remainingTime 1 s) ‖G‖ _ htest
    calc
      _ ≤ ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
          (ENNReal.ofReal ‖G‖*(pathLaw (survival (-δ) (remainingTime 1 s))/ENNReal.ofReal δ)) :=
        mul_le_mul' le_rfl htestbound
      _ = ENNReal.ofReal ‖G‖*((∫⁻ a in Ioi (0 : ℝ),
          BrownianFirstPassageDensityGeometry.density a s)*
            (pathLaw (survival (-δ) (remainingTime 1 s))/ENNReal.ofReal δ)) := by
        rw [passage_level_mass s hs.1]
        ac_rfl
      _ ≤ ENNReal.ofReal ‖G‖*ENNReal.ofReal (majorantCoefficient*timeMajorant 1 s) :=
        mul_le_mul' le_rfl (normalized_level_survival_mass_bound 1 s hs δ hδ)
      _ = _ := by rw [← ENNReal.ofReal_mul (norm_nonneg _),← mul_assoc]
  have hfin : (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (C*timeMajorant 1 s)) ≠ ⊤ := by
    simp_rw [ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul _ (measurable_timeMajorant 1).ennreal_ofReal]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_timeMajorant_ne_top 1 zero_lt_one)
  have ht := tendsto_lintegral_filter_of_dominated_convergence
    (fun s ↦ ENNReal.ofReal (C*timeMajorant 1 s)) (Eventually.of_forall hm) hbnd hfin
    ((ae_restrict_mem measurableSet_Ioo).mono (fun s hs ↦
      rawKernel_tendsto n times hstrict hzero hlast b hb κ hκ hcut G hG s hs))
  rw [lintegral_mul_const _ (measurable_timeWeight κ)] at ht
  exact ht

private theorem cutoff_unitMinimumFuture_test (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1)
    (b : ℝ≥0) (hb : b < 1) (κ : ℝ≥0 →ᵇ ℝ) (hκ : ∀ s, 0 ≤ κ s ∧ κ s ≤ 1)
    (hcut : ∀ s, b ≤ s → κ s = 0) (G : FreeVector (n+1) →ᵇ ℝ) (hG : ∀ v, 0 ≤ G v) :
    (∫⁻ f, ENNReal.ofReal (κ (leastMinimizer 1 f)*
      G (fun i : Fin (n+1) ↦ unitMinimumFuture f (times i.succ))) ∂pathLaw) =
      (∫⁻ s in Ioo (0 : ℝ) 1, timeWeight κ s)*
        ∫⁻ v, ENNReal.ofReal (G v) ∂freeEntranceLaw n (orderedGaps (n+1) times) := by
  let ε : ℝ≥0 := 1-b
  have hε : 0 < ε := tsub_pos_iff_lt.mpr hb
  let Ψ := splitTest n times ε hε κ G
  have hΨ : ∀ p, 0 ≤ Ψ p := fun p ↦ mul_nonneg (hκ _).1 (hG _)
  have hactual := BrownianMinimumSplitWindowNonnegativeLimit.actual_split_past_future_product_limit
    1 zero_lt_one Ψ hΨ
  have htime := rawKernel_time_tendsto n times hstrict hzero hlast b hb κ hκ hcut G hG
  have hactual' := hactual.congr (fun δ ↦ product_window_eq_time n times ε hε κ G δ)
  have hid := tendsto_nhds_unique hactual' htime
  have he (f : Path) : Ψ (minimumPoint 1 f) = κ (leastMinimizer 1 f)*
      G (fun i : Fin (n+1) ↦ unitMinimumFuture f (times i.succ)) := by
    by_cases hk : κ (leastMinimizer 1 f) = 0
    · simp only [Ψ,splitTest,rawTest,BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk,BoundedContinuousFunction.mul_apply,minimumPoint,hk,zero_mul]
    · have hs : leastMinimizer 1 f < b := lt_of_not_ge (fun h ↦ hk (hcut _ h))
      have hsc : scale ε (leastMinimizer 1 f) = remainingDuration f :=
        scale_eq_remaining b _ hs
      change κ (leastMinimizer 1 f)*G (relativeTuple n times ε
        (leastMinimizer 1 f,futurePath (leastMinimizer 1 f) f)) = _
      congr 2
      funext i
      rw [relativeTuple,hsc,unitMinimumFuture_eval,futurePath_eval,leastMinimizer_value]
  simpa only [he] using hid

private def baseWeight (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1/Real.sqrt (2*Real.pi))*timeMajorant 1 s)

private theorem measurable_baseWeight : Measurable baseWeight :=
  ((measurable_timeMajorant 1).const_mul _).ennreal_ofReal

private theorem baseWeight_ne_top : (∫⁻ s in Ioo (0 : ℝ) 1, baseWeight s) ≠ ⊤ := by
  unfold baseWeight
  simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/Real.sqrt (2*Real.pi))]
  rw [lintegral_const_mul _ (measurable_timeMajorant 1).ennreal_ofReal]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_timeMajorant_ne_top 1 zero_lt_one)

private theorem entranceTest_ne_top (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (G : FreeVector (n+1) →ᵇ ℝ) :
    (∫⁻ v, ENNReal.ofReal (G v) ∂freeEntranceLaw n (orderedGaps (n+1) times)) ≠ ⊤ := by
  let := freeEntranceLaw_isFinite n (orderedGaps (n+1) times) (orderedGaps_positive (n+1) times hstrict)
  have hb := lintegral_mono (μ := freeEntranceLaw n (orderedGaps (n+1) times))
    (fun v ↦ ENNReal.ofReal_le_ofReal ((le_abs_self (G v)).trans (G.norm_coe_le_norm v)))
  rw [lintegral_const] at hb
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hb

private def cutRadius (k : ℕ) : ℝ≥0 := 1-((k : ℝ≥0)+2)⁻¹
private def cutTerminal (k : ℕ) : ℝ≥0 := 1-((k : ℝ≥0)+2)⁻¹/2

private theorem cutRadius_lt_cutTerminal (k : ℕ) : cutRadius k < cutTerminal k := by
  have he : 0 < ((k : ℝ≥0)+2)⁻¹ := by positivity
  have hden : (1 : ℝ≥0) ≤ (k : ℝ≥0)+2 := by
    exact_mod_cast (show (1 : ℝ) ≤ (k : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) k])
  have he1 : ((k : ℝ≥0)+2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
  have hh : ((k : ℝ≥0)+2)⁻¹/2 ≤ 1 :=
    (div_le_self (by positivity) (by norm_num : (1 : ℝ≥0) ≤ 2)).trans he1
  change 1-((k : ℝ≥0)+2)⁻¹ < 1-((k : ℝ≥0)+2)⁻¹/2
  rw [← NNReal.coe_lt_coe,NNReal.coe_sub he1,NNReal.coe_sub hh]
  have heR : 0 < ((((k : ℝ≥0)+2)⁻¹ : ℝ≥0) : ℝ) := he
  simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
  linarith

private theorem cutTerminal_lt_one (k : ℕ) : cutTerminal k < 1 :=
  tsub_lt_self zero_lt_one (by positivity)

private theorem cutRadius_tendsto : Tendsto cutRadius atTop (𝓝 1) := by
  change Tendsto (fun k : ℕ ↦ (1 : ℝ≥0)-((k : ℝ≥0)+2)⁻¹) atTop (𝓝 1)
  have ht : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0)+2)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat 2).2
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
    simpa only [Nat.cast_add,Nat.cast_ofNat] using h
  simpa only [tsub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ≥0)) atTop (𝓝 1)).sub ht

private theorem unitMinimumFuture_test_factor (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1)
    (G : FreeVector (n+1) →ᵇ ℝ) (hG : ∀ v, 0 ≤ G v) :
    (∫⁻ f, ENNReal.ofReal (G (fun i : Fin (n+1) ↦ unitMinimumFuture f (times i.succ))) ∂pathLaw) =
      (∫⁻ s in Ioo (0 : ℝ) 1, baseWeight s)*
        ∫⁻ v, ENNReal.ofReal (G v) ∂freeEntranceLaw n (orderedGaps (n+1) times) := by
  have hex (k : ℕ) := ContinuousTimeCutoff.exists_timeCutoff
    (cutRadius k) (cutTerminal k) (cutRadius_lt_cutTerminal k)
  choose κ hκ hone hcut using hex
  have hκlim (s : ℝ≥0) (hs : s < 1) : Tendsto (fun k : ℕ ↦ κ k s) atTop (𝓝 (1 : ℝ)) := by
    have he : ∀ᶠ k : ℕ in atTop, s ≤ cutRadius k :=
      (cutRadius_tendsto.eventually (eventually_gt_nhds hs)).mono (fun _ h ↦ h.le)
    exact tendsto_const_nhds.congr' (he.mono (fun k hk ↦ (hone k s hk).symm))
  have hm (k : ℕ) : Measurable (fun f : Path ↦ ENNReal.ofReal
      (κ k (leastMinimizer 1 f)*G (fun i : Fin (n+1) ↦ unitMinimumFuture f (times i.succ)))) :=
    (((κ k).continuous.measurable.comp (measurable_leastMinimizer 1)).mul
      (G.continuous.measurable.comp (measurable_pi_lambda _
        (fun i ↦ (continuous_eval (times i.succ)).measurable.comp measurable_unitMinimumFuture)))).ennreal_ofReal
  have hb : ∀ k : ℕ, ∀ᵐ f ∂pathLaw, ENNReal.ofReal
      (κ k (leastMinimizer 1 f)*G (fun i : Fin (n+1) ↦ unitMinimumFuture f (times i.succ))) ≤
        ENNReal.ofReal ‖G‖ := by
    intro k
    apply Eventually.of_forall
    intro f
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_right (hκ k _).2 (hG _)).trans
      (by simpa only [one_mul] using (le_abs_self _).trans (G.norm_coe_le_norm _))
  have hsource := tendsto_lintegral_filter_of_dominated_convergence (μ := pathLaw)
    (fun _f ↦ ENNReal.ofReal ‖G‖) (Eventually.of_forall hm) (Eventually.of_forall hb)
    (by simp only [lintegral_const,measure_univ,mul_one]; exact ENNReal.ofReal_ne_top)
    ((BrownianPathFiniteReversal.ae_leastMinimizer_interior 1 zero_lt_one).mono
      (fun f hf ↦ by
        simpa only [one_mul] using ENNReal.tendsto_ofReal
          ((hκlim (leastMinimizer 1 f) hf.2).mul_const
            (G (fun i : Fin (n+1) ↦ unitMinimumFuture f (times i.succ))))))
  have hweightbound (k : ℕ) : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1),
      timeWeight (κ k) s ≤ baseWeight s := by
    apply Eventually.of_forall
    intro s
    change ENNReal.ofReal (κ k (Real.toNNReal s))*baseWeight s ≤ baseWeight s
    exact (mul_le_mul' (by simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (hκ k _).2) le_rfl).trans_eq (one_mul _)
  have hweightlim : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1),
      Tendsto (fun k : ℕ ↦ timeWeight (κ k) s) atTop (𝓝 (baseWeight s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsn : Real.toNNReal s < (1 : ℝ≥0) := by
      have he := Real.coe_toNNReal s hs.1.le
      exact_mod_cast (he.trans_lt hs.2)
    have h := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (hκlim _ hsn))
      (b := baseWeight s) (Or.inr ENNReal.ofReal_ne_top)
    simpa only [timeWeight,baseWeight,ENNReal.ofReal_one,one_mul] using h
  have hweight := tendsto_lintegral_filter_of_dominated_convergence baseWeight
    (Eventually.of_forall (fun k ↦ measurable_timeWeight (κ k)))
    (Eventually.of_forall hweightbound) baseWeight_ne_top hweightlim
  have hright := ENNReal.Tendsto.mul_const hweight (b := ∫⁻ v, ENNReal.ofReal (G v)
      ∂freeEntranceLaw n (orderedGaps (n+1) times))
    (Or.inr (entranceTest_ne_top n times hstrict G))
  have hsource' := hsource.congr (fun k ↦ cutoff_unitMinimumFuture_test n times hstrict hzero hlast
    (cutTerminal k) (cutTerminal_lt_one k) (κ k) (hκ k) (hcut k) G hG)
  exact tendsto_nhds_unique hsource' hright

theorem unitSource_prefix_nonnegative_test (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1)
    (G : FreeVector (n+1) →ᵇ ℝ) (hG : ∀ v, 0 ≤ G v) :
    (∫⁻ g, ENNReal.ofReal (G (fun i : Fin (n+1) ↦ g (times i.succ))) ∂unitSourceLaw) =
      (∫⁻ v, ENNReal.ofReal (G v) ∂freeEntranceLaw n (orderedGaps (n+1) times))/
        ENNReal.ofReal (Real.sqrt (2/Real.pi)) := by
  have hm : Measurable (fun g : Path ↦ ENNReal.ofReal
      (G (fun i : Fin (n+1) ↦ g (times i.succ)))) :=
    (G.continuous.measurable.comp (measurable_pi_lambda _
      (fun i ↦ (continuous_eval (times i.succ)).measurable))).ennreal_ofReal
  rw [unitSourceLaw,lintegral_map hm measurable_unitMinimumFuture]
  rw [unitMinimumFuture_test_factor n times hstrict hzero hlast G hG]
  have hn := unitMinimumFuture_test_factor n times hstrict hzero hlast
    (BoundedContinuousFunction.const _ (1 : ℝ)) (fun _ ↦ zero_le_one)
  simp only [BoundedContinuousFunction.const_apply',ENNReal.ofReal_one,lintegral_const,
    measure_univ,one_mul] at hn
  rw [BrownianFreeEntranceUnitMass.freeEntranceLaw_unit_mass n times hstrict hzero hlast] at hn
  have hM : ENNReal.ofReal (Real.sqrt (2/Real.pi)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))
  have hW : (∫⁻ s in Ioo (0 : ℝ) 1, baseWeight s) =
      1/ENNReal.ofReal (Real.sqrt (2/Real.pi)) :=
    (ENNReal.eq_div_iff hM ENNReal.ofReal_ne_top).mpr (by simpa only [mul_comm] using hn.symm)
  rw [hW]
  simp only [div_eq_mul_inv,one_mul,mul_comm]

theorem actual_unitSource_prefix_law (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1) :
    unitSourceLaw.map (fun g : Path ↦ fun i : Fin (n+1) ↦ g (times i.succ)) =
      (ENNReal.ofReal (Real.sqrt (2/Real.pi)))⁻¹ •
        freeEntranceLaw n (orderedGaps (n+1) times) := by
  have hm : Measurable (fun g : Path ↦ fun i : Fin (n+1) ↦ g (times i.succ)) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_eval (times i.succ)).measurable)
  let : IsProbabilityMeasure (unitSourceLaw.map (fun g : Path ↦ fun i : Fin (n+1) ↦ g (times i.succ))) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro Ψ
  have hΨ : Measurable (fun v : FreeVector (n+1) ↦ (Ψ v : ℝ≥0∞)) :=
    ENNReal.continuous_coe.measurable.comp Ψ.continuous.measurable
  rw [lintegral_map hΨ hm,lintegral_smul_measure,smul_eq_mul]
  let G : FreeVector (n+1) →ᵇ ℝ :=
    ⟨⟨fun v ↦ (Ψ v : ℝ),NNReal.continuous_coe.comp Ψ.continuous⟩,Ψ.map_bounded'⟩
  have h := unitSource_prefix_nonnegative_test n times hstrict hzero hlast G
    (fun v ↦ (Ψ v).coe_nonneg)
  simpa only [G,BoundedContinuousFunction.coe_mk,ENNReal.ofReal_coe_nnreal,
    div_eq_mul_inv,mul_comm] using h

theorem unitSource_prefix_borel_test (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1)
    (H : FreeVector (n+1) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ g, H (fun i : Fin (n+1) ↦ g (times i.succ)) ∂unitSourceLaw) =
      (∫⁻ v, H v ∂freeEntranceLaw n (orderedGaps (n+1) times))/
        ENNReal.ofReal (Real.sqrt (2/Real.pi)) := by
  have hm : Measurable (fun g : Path ↦ fun i : Fin (n+1) ↦ g (times i.succ)) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_eval (times i.succ)).measurable)
  rw [← lintegral_map hH hm,actual_unitSource_prefix_law n times hstrict hzero hlast,
    lintegral_smul_measure,smul_eq_mul]
  simp only [div_eq_mul_inv,mul_comm]

end PerronWright.BrownianMinimumFuturePrefixTests
