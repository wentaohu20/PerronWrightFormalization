import PerronWright.Probability.BrownianPositiveBridgeFiniteCoordinateMoments
import PerronWright.Probability.BrownianPositiveBridgeMultiPointGlobalTests

/-! # Actual entrance-coordinate moments obtained from the path source

The literal entrance product is the previously normalized probability
measure.  Fatou's lemma transfers the genuine uniform path-coordinate
bound to this measure; finiteness is proved rather than imposed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeEntranceCoordinateMoments

open BrownianPathLaw BrownianPositiveBridgeConditioning
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianPositiveBridgeMultiPointCoordinates BrownianPositiveBridgeMultiPointLaw
open BrownianPositiveBridgeMultiPointEntrance BrownianPositiveBridgeMultiPointMass
open BrownianPositiveBridgeMultiPointActualTests BrownianPositiveBridgeMultiPointGlobalTests
open BrownianPositiveBridgeFiniteCoordinateMoments

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem positive_finalTime (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) : 0 < sampleTime gaps (n+2) := by
  rw [sampleTime_succ]
  exact (hgaps (n+1) (by omega)).trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))

theorem eventually_raw_radius_moment_bound (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (k : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ v : FreeVector (n+1), rawMultiDensity n a gaps v*ENNReal.ofReal (radius v^k)) ≤
        jointMomentBound (sampleTime gaps (n+2)) (n+1) k := by
  have hT := positive_finalTime n gaps hgaps
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_finite_coordinate_moment
    (sampleTime gaps (n+2)) hT (n+1) k] with a ha hb
  have he := multiPoint_lintegral (n+1) a ha gaps
    (fun j hj ↦ hgaps j (by omega)) (hgaps (n+1) (by omega))
    (fun v : FreeVector (n+1) ↦ ENNReal.ofReal (radius v^k))
    (((continuous_radius _).pow k).measurable.ennreal_ofReal)
  rw [← rawMultiDensity_eq_actual_density] at he
  rw [← he]
  exact hb (internalTimes (n+1) gaps) (internalTimes_le_final (n+1) gaps)

theorem entrance_radius_moment_bound (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (k : ℕ) :
    (∫⁻ v : FreeVector (n+1), ENNReal.ofReal (radius v^k) ∂entranceLaw n gaps) ≤
      jointMomentBound (sampleTime gaps (n+2)) (n+1) k := by
  have hm : Measurable (fun v : FreeVector (n+1) ↦ ENNReal.ofReal (radius v^k)) :=
    ((continuous_radius _).pow k).measurable.ennreal_ofReal
  have hp (v : FreeVector (n+1)) : Tendsto
      (fun a : ℝ ↦ rawMultiDensity n a gaps v*ENNReal.ofReal (radius v^k)) (𝓝[>] 0)
      (𝓝 (entranceProduct n gaps v*ENNReal.ofReal (radius v^k))) :=
    ENNReal.Tendsto.mul_const (rawMultiDensity_tendsto n gaps
      (hgaps 0 (by omega)) (hgaps (n+1) (by omega)) (positive_finalTime n gaps hgaps) v)
      (Or.inr ENNReal.ofReal_ne_top)
  rw [entranceLaw,lintegral_withDensity_eq_lintegral_mul volume (measurable_entranceProduct n gaps) hm]
  calc
    _ = ∫⁻ v : FreeVector (n+1), liminf
        (fun a : ℝ ↦ rawMultiDensity n a gaps v*ENNReal.ofReal (radius v^k)) (𝓝[>] 0) :=
      lintegral_congr (fun v ↦ (hp v).liminf_eq.symm)
    _ ≤ liminf (fun a : ℝ ↦ ∫⁻ v : FreeVector (n+1),
        rawMultiDensity n a gaps v*ENNReal.ofReal (radius v^k)) (𝓝[>] 0) :=
      lintegral_liminf_le (fun a ↦ (measurable_rawMultiDensity n a gaps).mul hm)
    _ ≤ limsup (fun a : ℝ ↦ ∫⁻ v : FreeVector (n+1),
        rawMultiDensity n a gaps v*ENNReal.ofReal (radius v^k)) (𝓝[>] 0) := liminf_le_limsup
    _ ≤ _ := limsup_le_of_le (by isBoundedDefault) (eventually_raw_radius_moment_bound n gaps hgaps k)

theorem entrance_radius_moment_lt_top (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (k : ℕ) :
    (∫⁻ v : FreeVector (n+1), ENNReal.ofReal (radius v^k) ∂entranceLaw n gaps) < ∞ :=
  (entrance_radius_moment_bound n gaps hgaps k).trans_lt
    (jointMomentBound_lt_top _ (positive_finalTime n gaps hgaps) _ _)

theorem entrance_radius_pow_integrable (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (k : ℕ) :
    Integrable (fun v : FreeVector (n+1) ↦ radius v^k) (entranceLaw n gaps) := by
  refine ⟨((continuous_radius _).pow k).aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun v ↦ pow_nonneg (zero_le_one.trans (one_le_radius v)) k))).mpr
    (entrance_radius_moment_lt_top n gaps hgaps k)

theorem entrance_radius_tail_moment_bound (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (k : ℕ) {B : ℝ} (hB : 0 < B) :
    (∫⁻ v : FreeVector (n+1) in {v : FreeVector (n+1) | B ≤ radius v},
      ENNReal.ofReal (radius v^k) ∂entranceLaw n gaps) ≤
        jointMomentBound (sampleTime gaps (n+2)) (n+1) (k+1)/ENNReal.ofReal B := by
  calc
    _ ≤ ∫⁻ v : FreeVector (n+1) in {v : FreeVector (n+1) | B ≤ radius v},
        ENNReal.ofReal (radius v^(k+1))/ENNReal.ofReal B ∂entranceLaw n gaps := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_const (continuous_radius _).measurable)] with v hv
      exact radius_tail_power_le_succ v k hB hv
    _ ≤ ∫⁻ v : FreeVector (n+1), ENNReal.ofReal (radius v^(k+1))/ENNReal.ofReal B ∂entranceLaw n gaps :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = (∫⁻ v : FreeVector (n+1), ENNReal.ofReal (radius v^(k+1)) ∂entranceLaw n gaps)/ENNReal.ofReal B := by
      simp only [div_eq_mul_inv]
      have hm : Measurable (fun v : FreeVector (n+1) ↦ ENNReal.ofReal (radius v^(k+1))) :=
        ((continuous_radius _).pow (k+1)).measurable.ennreal_ofReal
      exact lintegral_mul_const _ hm
    _ ≤ _ := ENNReal.div_le_div_right (entrance_radius_moment_bound n gaps hgaps (k+1)) _

end PerronWright.BrownianPositiveBridgeEntranceCoordinateMoments
