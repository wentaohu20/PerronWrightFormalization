import PerronWright.Probability.BrownianKilledFreeEntranceGeometry
import PerronWright.Probability.BrownianKilledGlobalEntranceTests
import PerronWright.Probability.BrownianKilledFiniteDimensionalOrderedDensity

/-! # Actual one-boundary killed finite-dimensional entrance limits

Every finite ordered nonempty tuple, including its survival terminal time,
has a genuine entrance limit against bounded continuous joint tests. The
first Gaussian envelope is integrated against the actual remaining killed
chain, whose total mass is at most one. No FDD or weak limit is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledFreeEntranceTests

open BrownianPathLaw ContinuousPathFirstPassage
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalDensity
open BrownianKilledFiniteDimensionalOrderedDensity
open BrownianKilledFreeEntranceGeometry BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeMultiPointEntrance BrownianPositiveBridgeGaussianBounds
open BrownianKilledGlobalEntranceTests

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def envelopeJoint (n : ℕ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  ENNReal.ofReal (envelopeReal (gaps 0) (gaps 0) (v 0))*internalDensity n gaps v

theorem measurable_envelopeJoint (n : ℕ) (gaps : ℕ → ℝ≥0) : Measurable (envelopeJoint n gaps) :=
  (((measurable_envelopeReal _ _).comp (measurable_pi_apply 0)).ennreal_ofReal).mul
    (measurable_internalDensity n gaps)

theorem lintegral_envelopeJoint_le (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+1, 0 < gaps j) :
    (∫⁻ v, envelopeJoint n gaps v) ≤ ∫⁻ y, ENNReal.ofReal (envelopeReal (gaps 0) (gaps 0) y) := by
  rw [lintegral_volume_freeCons n (measurable_envelopeJoint n gaps)]
  apply lintegral_mono
  intro y
  simp only [envelopeJoint]
  simp_rw [internalDensity_freeCons]
  simp only [freeCons,Fin.cons_zero]
  rw [lintegral_const_mul _ (measurable_jointDensity n y (fun j ↦ gaps (j+1)))]
  exact (mul_le_mul' le_rfl (jointDensity_lintegral_le_one n y (fun j ↦ gaps (j+1))
    (fun j hj ↦ hgaps (j+1) (by omega)))).trans_eq (mul_one _)

theorem lintegral_envelopeJoint_ne_top (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+1, 0 < gaps j) : (∫⁻ v, envelopeJoint n gaps v) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (lintegral_envelopeJoint_le n gaps hgaps)
  exact ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (envelopeReal_nonneg _ _))).mp
    (integrable_envelopeReal _ _ (hgaps 0 (by omega))).hasFiniteIntegral).ne

theorem integrable_real_envelopeJoint (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+1, 0 < gaps j) :
    Integrable (fun v : FreeVector (n+1) ↦
      envelopeReal (gaps 0) (gaps 0) (v 0)*(internalDensity n gaps v).toReal) := by
  have hi := integrable_toReal_of_lintegral_ne_top (measurable_envelopeJoint n gaps).aemeasurable
    (lintegral_envelopeJoint_ne_top n gaps hgaps)
  simpa only [envelopeJoint,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (envelopeReal_nonneg _ _ _)] using hi

theorem entranceJoint_lintegral_ne_top (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+1, 0 < gaps j) : (∫⁻ v, entranceJoint n gaps v) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (lintegral_envelopeJoint_ne_top n gaps hgaps)
  apply lintegral_mono
  intro v
  have he : entranceReal (gaps 0) (v 0) ≤ envelopeReal (gaps 0) (gaps 0) (v 0) := by
    apply le_of_tendsto (densityReal_div_start_tendsto _ (hgaps 0 (by omega)) (v 0))
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with a ha ha1
    exact densityReal_div_start_le_envelope a ha ha1.le _ _ _ (hgaps 0 (by omega))
      le_rfl le_rfl (v 0)
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal he) le_rfl

def freeEntranceLaw (n : ℕ) (gaps : ℕ → ℝ≥0) : Measure (FreeVector (n+1)) :=
  volume.withDensity (entranceJoint n gaps)

theorem freeEntranceLaw_isFinite (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+1, 0 < gaps j) : IsFiniteMeasure (freeEntranceLaw n gaps) := by
  constructor
  rw [freeEntranceLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact lt_top_iff_ne_top.mpr (entranceJoint_lintegral_ne_top n gaps hgaps)

theorem normalized_freeTuple_real_test_eq_density (n : ℕ) (a : ℝ) (ha : 0 < a)
    (gaps : ℕ → ℝ≥0) (hgaps : ∀ j < n+1, 0 < gaps j) (G : FreeVector (n+1) → ℝ) :
    (∫ v, G v ∂freeTupleLaw a gaps (n+1))/a =
      ∫ v, densityReal a (gaps 0) (v 0)/a*(internalDensity n gaps v).toReal*G v := by
  have hn (v : FreeVector (n+1)) : jointDensity (n+1) a gaps v < ⊤ := by
    rw [jointDensity_first_factor]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (internalDensity_ne_top n gaps v))
  rw [freeTupleLaw_eq_withDensity (n+1) a ha gaps hgaps,
    integral_withDensity_eq_integral_toReal_smul (measurable_jointDensity (n+1) a gaps)
      (Eventually.of_forall hn)]
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv,← integral_mul_const]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro v
  dsimp only
  rw [jointDensity_first_factor,ENNReal.toReal_mul]
  simp only [density,ENNReal.toReal_ofReal (densityReal_nonneg a ha _ (hgaps 0 (by omega)) _)]
  ring

theorem normalized_freeTuple_bounded_continuous_test_tendsto (n : ℕ)
    (gaps : ℕ → ℝ≥0) (hgaps : ∀ j < n+1, 0 < gaps j)
    (G : (ℝ × FreeVector (n+1)) →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ (∫ v, G (a,v) ∂freeTupleLaw a gaps (n+1))/a) (𝓝[>] 0)
      (𝓝 (∫ v, G (0,v) ∂freeEntranceLaw n gaps)) := by
  have hm (a : ℝ) : AEStronglyMeasurable (fun v : FreeVector (n+1) ↦
      densityReal a (gaps 0) (v 0)/a*(internalDensity n gaps v).toReal*G (a,v)) volume :=
    (((((measurable_densityReal a _).comp (measurable_pi_apply 0)).div_const a).mul
      (measurable_internalDensity n gaps).ennreal_toReal).mul
      (G.continuous.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have hb : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ v : FreeVector (n+1),
      ‖densityReal a (gaps 0) (v 0)/a*(internalDensity n gaps v).toReal*G (a,v)‖ ≤
        (envelopeReal (gaps 0) (gaps 0) (v 0)*(internalDensity n gaps v).toReal)*‖G‖ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with a ha ha1
    apply Eventually.of_forall
    intro v
    rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg
      (div_nonneg (densityReal_nonneg a ha _ (hgaps 0 (by omega)) _) ha.le),
      Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul (mul_le_mul_of_nonneg_right
      (densityReal_div_start_le_envelope a ha ha1.le _ _ _ (hgaps 0 (by omega)) le_rfl le_rfl _) 
      ENNReal.toReal_nonneg) (G.norm_coe_le_norm _) (norm_nonneg _)
      (mul_nonneg (envelopeReal_nonneg _ _ _) ENNReal.toReal_nonneg)
  have hi := (integrable_real_envelopeJoint n gaps hgaps).mul_const ‖G‖
  have hl : ∀ᵐ v : FreeVector (n+1), Tendsto (fun a : ℝ ↦
      densityReal a (gaps 0) (v 0)/a*(internalDensity n gaps v).toReal*G (a,v)) (𝓝[>] 0)
      (𝓝 (entranceReal (gaps 0) (v 0)*(internalDensity n gaps v).toReal*G (0,v))) :=
    Eventually.of_forall (fun v ↦ ((densityReal_div_start_tendsto _ (hgaps 0 (by omega)) (v 0)).mul_const
      (internalDensity n gaps v).toReal).mul (G.continuous.tendsto _ |>.comp
        (tendsto_id.mono_left nhdsWithin_le_nhds |>.prodMk_nhds tendsto_const_nhds)))
  have hdct := tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hm) hb hi hl
  have he : (∫ v, G (0,v) ∂freeEntranceLaw n gaps) =
      ∫ v, entranceReal (gaps 0) (v 0)*(internalDensity n gaps v).toReal*G (0,v) := by
    rw [freeEntranceLaw,integral_withDensity_eq_integral_toReal_smul (measurable_entranceJoint n gaps)
      (Eventually.of_forall (fun v ↦ lt_top_iff_ne_top.mpr (entranceJoint_ne_top n gaps v)))]
    simp only [entranceJoint,entrance,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (entranceReal_nonneg _ _),smul_eq_mul]
  rw [he]
  apply hdct.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (normalized_freeTuple_real_test_eq_density n a ha gaps hgaps (fun v ↦ G (a,v))).symm

theorem actual_bounded_continuous_test_tendsto (n : ℕ)
    (gaps : ℕ → ℝ≥0) (hgaps : ∀ j < n+1, 0 < gaps j)
    (G : (ℝ × FreeVector (n+1)) →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ (∫ f in survival (-a) (sampleTime gaps (n+1)),
      G (a,fun i : Fin (n+1) ↦ a+f (sampleTime gaps (i.val+1))) ∂pathLaw)/a) (𝓝[>] 0)
      (𝓝 (∫ v, G (0,v) ∂freeEntranceLaw n gaps)) := by
  apply (normalized_freeTuple_bounded_continuous_test_tendsto n gaps hgaps G).congr
  intro a
  rw [freeTupleLaw_eq_source]
  have hm : Measurable (fun f : Path ↦ fun i : Fin (n+1) ↦ a+f (sampleTime gaps (i.val+1))) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_const.add (continuous_eval _).measurable)
  have hg : Continuous (fun v : FreeVector (n+1) ↦ G (a,v)) := by fun_prop
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]

theorem actual_ordered_bounded_continuous_test_tendsto (n : ℕ)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (G : (ℝ × FreeVector (n+1)) →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ (∫ f in survival (-a) (times (Fin.last (n+1))),
      G (a,fun i : Fin (n+1) ↦ a+f (times i.succ)) ∂pathLaw)/a) (𝓝[>] 0)
      (𝓝 (∫ v, G (0,v) ∂freeEntranceLaw n (orderedGaps (n+1) times))) := by
  apply (normalized_freeTuple_bounded_continuous_test_tendsto n (orderedGaps (n+1) times)
    (orderedGaps_positive (n+1) times hstrict) G).congr
  intro a
  rw [freeTupleLaw_ordered_source a (n+1) times hstrict.monotone hzero]
  have hm : Measurable (fun f : Path ↦ fun i : Fin (n+1) ↦ a+f (times i.succ)) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_const.add (continuous_eval _).measurable)
  have hg : Continuous (fun v : FreeVector (n+1) ↦ G (a,v)) := by fun_prop
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable]

theorem actual_unshifted_ordered_test_tendsto (n : ℕ)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (G : (ℝ × FreeVector (n+1)) →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ (∫ f in survival (-a) (times (Fin.last (n+1))),
      G (a,fun i : Fin (n+1) ↦ f (times i.succ)) ∂pathLaw)/a) (𝓝[>] 0)
      (𝓝 (∫ v, G (0,v) ∂freeEntranceLaw n (orderedGaps (n+1) times))) := by
  let shift : C(ℝ × FreeVector (n+1),ℝ × FreeVector (n+1)) :=
    ⟨fun p ↦ (p.1,fun i ↦ p.2 i-p.1),by fun_prop⟩
  have h := actual_ordered_bounded_continuous_test_tendsto n times hstrict hzero (G.compContinuous shift)
  simpa only [BoundedContinuousFunction.compContinuous_apply,shift,ContinuousMap.coe_mk,
    add_sub_cancel_left,sub_zero] using h

end PerronWright.BrownianKilledFreeEntranceTests
