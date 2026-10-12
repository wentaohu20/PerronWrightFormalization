import PerronWright.Probability.BrownianPositiveBridgeMultiPointMass
import PerronWright.Probability.BrownianPositiveBridgeMultiPointActualTests

/-! # Genuine full-state finite-dimensional positive-bridge limits

The overlap of the actual density and its now normalized entrance product
is dominated by the latter. Direct dominated convergence and the two proved
unit masses give vanishing positive density remainders. This proves global
bounded Borel coupled tests of the actual conditioned bridge, without a
uniform-integrability or path-convergence premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMultiPointGlobalTests

open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianPositiveBridgeMultiPointEntrance BrownianPositiveBridgeMultiPointMass
open BrownianPositiveBridgeMultiPointActualTests
open BrownianPositiveBridgeConditioning BrownianPositiveBridgeMultiPointCoordinates BrownianPositiveBridgeMultiPointLaw
open BrownianKilledFiniteDimensionalOrderedTimes BrownianKilledFiniteDimensionalOrderedDensity
open BrownianPositiveBridgeMultiPointOrderedLaw

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def overlap (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  min (rawMultiDensity n a gaps v) (entranceProduct n gaps v)

theorem measurable_overlap (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) : Measurable (overlap n a gaps) :=
  (measurable_rawMultiDensity n a gaps).min (measurable_entranceProduct n gaps)

theorem overlap_integral_ne_top (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) : (∫⁻ v, overlap n a gaps v) ≠ ∞ :=
  ne_top_of_le_ne_top (entranceProduct_integral_ne_top n gaps hgaps)
    (lintegral_mono (fun _v ↦ min_le_right _ _))

theorem overlap_bounded_test_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (Ψ : FreeVector (n+1) → ℝ≥0∞)
    (hΨ : Measurable Ψ) (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v, overlap n a gaps v*Ψ v) (𝓝[>] 0)
      (𝓝 (∫⁻ v, entranceProduct n gaps v*Ψ v)) := by
  have hm : ∀ᶠ a : ℝ in 𝓝[>] 0, Measurable (fun v ↦ overlap n a gaps v*Ψ v) :=
    Eventually.of_forall (fun a ↦ (measurable_overlap n a gaps).mul hΨ)
  have hbd : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ v ∂volume,
      overlap n a gaps v*Ψ v ≤ entranceProduct n gaps v*Ψ v :=
    Eventually.of_forall (fun _a ↦ Eventually.of_forall (fun _v ↦ mul_le_mul' (min_le_right _ _) le_rfl))
  have hfin : (∫⁻ v, entranceProduct n gaps v*Ψ v) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc
      _ ≤ ∫⁻ v, entranceProduct n gaps v*ENNReal.ofReal C :=
        lintegral_mono (fun v ↦ mul_le_mul' le_rfl (hbound v))
      _ = ENNReal.ofReal C := by
        rw [lintegral_mul_const _ (measurable_entranceProduct n gaps),entranceProduct_integral_eq_one n gaps hgaps,one_mul]
  have hT : 0 < sampleTime gaps (n+2) := by
    rw [sampleTime_succ]
    exact (hgaps (n+1) (by omega)).trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))
  have hlim : ∀ᵐ v ∂volume, Tendsto (fun a : ℝ ↦ overlap n a gaps v*Ψ v) (𝓝[>] 0)
      (𝓝 (entranceProduct n gaps v*Ψ v)) := by
    apply Eventually.of_forall
    intro v
    have ho : Tendsto (fun a : ℝ ↦ overlap n a gaps v) (𝓝[>] 0) (𝓝 (entranceProduct n gaps v)) := by
      simpa only [overlap,min_self] using (rawMultiDensity_tendsto n gaps
        (hgaps 0 (by omega)) (hgaps (n+1) (by omega)) hT v).min
          (tendsto_const_nhds (x := entranceProduct n gaps v))
    exact ENNReal.Tendsto.mul_const ho (Or.inr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound v)))
  exact tendsto_lintegral_filter_of_dominated_convergence (μ := volume)
    (fun v ↦ entranceProduct n gaps v*Ψ v) hm hbd hfin hlim

theorem overlap_integral_tendsto_one (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v, overlap n a gaps v) (𝓝[>] 0) (𝓝 (1 : ℝ≥0∞)) := by
  simpa only [mul_one,entranceProduct_integral_eq_one n gaps hgaps] using
    overlap_bounded_test_tendsto n gaps hgaps 1 (fun _ ↦ 1) measurable_const (fun _ ↦ by simp)

theorem density_remainder_integral_tendsto_zero (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v, rawMultiDensity n a gaps v-overlap n a gaps v)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have he : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ v, rawMultiDensity n a gaps v-overlap n a gaps v) = 1-(∫⁻ v, overlap n a gaps v) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [lintegral_sub (measurable_overlap n a gaps) (overlap_integral_ne_top n a gaps hgaps)
      (Eventually.of_forall (fun v ↦ min_le_left _ _)),rawMultiDensity_integral n a ha gaps hgaps]
  have ht := ENNReal.Tendsto.sub tendsto_const_nhds (overlap_integral_tendsto_one n gaps hgaps)
    (Or.inl (show (1 : ℝ≥0∞) ≠ ∞ by simp))
  apply (show Tendsto (fun a : ℝ ↦ 1-(∫⁻ v, overlap n a gaps v)) (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) from by
    simpa only [tsub_self] using ht).congr'
  exact he.mono (fun _a ha ↦ ha.symm)

theorem global_bounded_test_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (Ψ : FreeVector (n+1) → ℝ≥0∞)
    (hΨ : Measurable Ψ) (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v, rawMultiDensity n a gaps v*Ψ v) (𝓝[>] 0)
      (𝓝 (∫⁻ v, entranceProduct n gaps v*Ψ v)) := by
  have hlo := overlap_bounded_test_tendsto n gaps hgaps C Ψ hΨ hbound
  have hr := ENNReal.Tendsto.mul_const (density_remainder_integral_tendsto_zero n gaps hgaps)
    (Or.inr (show ENNReal.ofReal C ≠ ∞ from ENNReal.ofReal_ne_top))
  have hhi : Tendsto (fun a : ℝ ↦ (∫⁻ v, overlap n a gaps v*Ψ v)+
      (∫⁻ v, rawMultiDensity n a gaps v-overlap n a gaps v)*ENNReal.ofReal C)
      (𝓝[>] 0) (𝓝 (∫⁻ v, entranceProduct n gaps v*Ψ v)) := by
    simpa only [zero_mul,add_zero] using hlo.add hr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · exact Eventually.of_forall (fun a ↦ lintegral_mono (fun v ↦ mul_le_mul' (min_le_left _ _) le_rfl))
  · apply Eventually.of_forall
    intro a
    have hd : Measurable (fun v ↦ rawMultiDensity n a gaps v-overlap n a gaps v) :=
      (measurable_rawMultiDensity n a gaps).sub (measurable_overlap n a gaps)
    have hf : Measurable (fun v ↦ overlap n a gaps v*Ψ v) :=
      (measurable_overlap n a gaps).mul hΨ
    calc
      _ ≤ ∫⁻ v, overlap n a gaps v*Ψ v+
          (rawMultiDensity n a gaps v-overlap n a gaps v)*ENNReal.ofReal C := by
        apply lintegral_mono
        intro v
        calc
          _ = (overlap n a gaps v+(rawMultiDensity n a gaps v-overlap n a gaps v))*Ψ v := by
            have hv : overlap n a gaps v ≤ rawMultiDensity n a gaps v := min_le_left _ _
            rw [add_tsub_cancel_of_le hv]
          _ = _ := add_mul _ _ _
          _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl (hbound v))
      _ = _ := by rw [lintegral_add_left hf,lintegral_mul_const _ hd]

theorem actual_global_bounded_test_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (Ψ : FreeVector (n+1) → ℝ≥0∞)
    (hΨ : Measurable Ψ) (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g, Ψ (internalEval (n+1) gaps g)
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫⁻ v, Ψ v ∂entranceLaw n gaps)) := by
  rw [entranceLaw,lintegral_withDensity_eq_lintegral_mul volume (measurable_entranceProduct n gaps) hΨ]
  have he := global_bounded_test_tendsto n gaps hgaps C Ψ hΨ hbound
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [multiPoint_lintegral (n+1) a ha gaps (fun j hj ↦ hgaps j (by omega)) (hgaps (n+1) (by omega)) Ψ hΨ]
  rfl

theorem actual_ordered_global_bounded_test_tendsto (n : ℕ)
    (times : Fin (n+3) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (C : ℝ) (Ψ : FreeVector (n+1) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g, Ψ (fun i : Fin (n+1) ↦ g (times i.succ.castSucc))
        ∂positiveBridgeLaw a (times (Fin.last (n+2)))) (𝓝[>] 0)
      (𝓝 (∫⁻ v, Ψ v ∂entranceLaw n (orderedGaps (n+2) times))) := by
  have hgaps : ∀ j < n+2, 0 < orderedGaps (n+2) times j :=
    fun j hj ↦ orderedGaps_positive (n+2) times hstrict j hj
  have he := actual_global_bounded_test_tendsto n (orderedGaps (n+2) times) hgaps C Ψ hΨ hbound
  have hT := sampleTime_orderedGaps (n+2) times hstrict.monotone hzero (Fin.last (n+2))
  simp only [Fin.val_last] at hT
  rw [hT,internalEval_orderedGaps (n+1) times hstrict.monotone hzero] at he
  exact he

theorem actual_finiteDimensional_borel_probability_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) {B : Set (FreeVector (n+1))} (hB : MeasurableSet B) :
    Tendsto (fun a : ℝ ↦ ((positiveBridgeLaw a (sampleTime gaps (n+2))).map
        (internalEval (n+1) gaps)) B) (𝓝[>] 0) (𝓝 (entranceLaw n gaps B)) := by
  have h1 : (fun _ : FreeVector (n+1) ↦ (1 : ℝ≥0∞)) = (1 : FreeVector (n+1) → ℝ≥0∞) := rfl
  have he := actual_global_bounded_test_tendsto n gaps hgaps 1
    (B.indicator (fun _ ↦ 1)) (measurable_const.indicator hB)
    (fun v ↦ by by_cases hv : v ∈ B <;> simp only [Set.indicator,hv,if_true,if_false]; all_goals simp)
  have hlast : (∫⁻ v, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) v ∂entranceLaw n gaps) = entranceLaw n gaps B := by
    rw [h1]
    exact lintegral_indicator_one hB
  rw [hlast] at he
  apply he.congr
  intro a
  rw [← lintegral_map (measurable_const.indicator hB) (continuous_internalEval (n+1) gaps).measurable]
  rw [h1]
  exact lintegral_indicator_one hB

theorem entrance_remainder_integral_tendsto_zero (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v, entranceProduct n gaps v-overlap n a gaps v)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have he (a : ℝ) : (∫⁻ v, entranceProduct n gaps v-overlap n a gaps v) =
      1-(∫⁻ v, overlap n a gaps v) := by
    rw [lintegral_sub (measurable_overlap n a gaps) (overlap_integral_ne_top n a gaps hgaps)
      (Eventually.of_forall (fun _v ↦ min_le_right _ _)),entranceProduct_integral_eq_one n gaps hgaps]
  have ht := ENNReal.Tendsto.sub tendsto_const_nhds (overlap_integral_tendsto_one n gaps hgaps)
    (Or.inl (show (1 : ℝ≥0∞) ≠ ∞ by simp))
  apply (show Tendsto (fun a : ℝ ↦ 1-(∫⁻ v, overlap n a gaps v)) (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) from by
    simpa only [tsub_self] using ht).congr
  intro a
  exact (he a).symm

theorem density_l1_tendsto_zero (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v, (rawMultiDensity n a gaps v-entranceProduct n gaps v)+
        (entranceProduct n gaps v-rawMultiDensity n a gaps v)) (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have hleft : Tendsto (fun a : ℝ ↦ ∫⁻ v, rawMultiDensity n a gaps v-entranceProduct n gaps v)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [overlap,tsub_min] using density_remainder_integral_tendsto_zero n gaps hgaps
  have hright : Tendsto (fun a : ℝ ↦ ∫⁻ v, entranceProduct n gaps v-rawMultiDensity n a gaps v)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [overlap,min_comm,tsub_min] using entrance_remainder_integral_tendsto_zero n gaps hgaps
  have he := hleft.add hright
  simp only [zero_add] at he
  apply he.congr
  intro a
  have hm : Measurable (fun v ↦ rawMultiDensity n a gaps v-entranceProduct n gaps v) :=
    (measurable_rawMultiDensity n a gaps).sub (measurable_entranceProduct n gaps)
  exact (lintegral_add_left hm _).symm

end PerronWright.BrownianPositiveBridgeMultiPointGlobalTests
