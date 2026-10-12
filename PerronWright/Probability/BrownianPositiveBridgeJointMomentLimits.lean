import PerronWright.Probability.BrownianPositiveBridgeEntranceCoordinateMoments
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Genuine unbounded coupled coordinate tests of positive bridges

Polynomial growth is controlled by the actual joint moments. The
entrance moments were proved from the source. A weighted Cauchy--Schwarz
estimate makes the actual density remainder vanish, extending the
previous bounded-test limit without a moment/UI convergence premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeJointMomentLimits

open BrownianPathLaw BrownianPositiveBridgeConditioning
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledFiniteDimensionalOrderedTimes BrownianKilledFiniteDimensionalOrderedDensity
open BrownianPositiveBridgeMultiPointCoordinates BrownianPositiveBridgeMultiPointLaw
open BrownianPositiveBridgeMultiPointOrderedLaw
open BrownianPositiveBridgeMultiPointEntrance BrownianPositiveBridgeMultiPointMass
open BrownianPositiveBridgeMultiPointActualTests BrownianPositiveBridgeMultiPointGlobalTests
open BrownianPositiveBridgeFiniteCoordinateMoments BrownianPositiveBridgeEntranceCoordinateMoments

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem weighted_lintegral_le_half_moments {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {w Ψ : X → ℝ≥0∞} (hw : Measurable w) (hΨ : Measurable Ψ) :
    (∫⁻ v, w v*Ψ v ∂μ) ≤
      (∫⁻ v, w v ∂μ)^(1/2 : ℝ) * (∫⁻ v, w v*(Ψ v)^2 ∂μ)^(1/2 : ℝ) := by
  have hp (x y : ℝ≥0∞) : x^(1/2 : ℝ)*(x*y^2)^(1/2 : ℝ) = x*y := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2),
      ← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
    rw [← mul_assoc,← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
    norm_num
  calc
    _ = ∫⁻ v, (w v)^(1/2 : ℝ)*(w v*(Ψ v)^2)^(1/2 : ℝ) ∂μ :=
      lintegral_congr (fun v ↦ (hp (w v) (Ψ v)).symm)
    _ ≤ _ := ENNReal.lintegral_mul_norm_pow_le hw.aemeasurable
      (hw.mul (hΨ.pow_const 2)).aemeasurable (by norm_num) (by norm_num) (by norm_num)

theorem entrance_growth_test_bound (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (k : ℕ)
    (Ψ : FreeVector (n+1) → ℝ≥0∞)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C*ENNReal.ofReal (radius v^k)) :
    (∫⁻ v, Ψ v ∂entranceLaw n gaps) ≤
      ENNReal.ofReal C*jointMomentBound (sampleTime gaps (n+2)) (n+1) k := by
  calc
    _ ≤ ∫⁻ v, ENNReal.ofReal C*ENNReal.ofReal (radius v^k) ∂entranceLaw n gaps := lintegral_mono hbound
    _ = ENNReal.ofReal C*(∫⁻ v, ENNReal.ofReal (radius v^k) ∂entranceLaw n gaps) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (entrance_radius_moment_bound n gaps hgaps k)

theorem entrance_growth_test_lt_top (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (k : ℕ)
    (Ψ : FreeVector (n+1) → ℝ≥0∞)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C*ENNReal.ofReal (radius v^k)) :
    (∫⁻ v, Ψ v ∂entranceLaw n gaps) < ∞ := by
  apply (entrance_growth_test_bound n gaps hgaps C k Ψ hbound).trans_lt
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (jointMomentBound_lt_top _ (positive_finalTime n gaps hgaps) _ _)

theorem eventually_raw_growth_test_square_bound (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (Ψ : FreeVector (n+1) → ℝ≥0∞)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C*ENNReal.ofReal (radius v^k)) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ v, rawMultiDensity n a gaps v*(Ψ v)^2) ≤
        ENNReal.ofReal (C^2)*jointMomentBound (sampleTime gaps (n+2)) (n+1) (2*k) := by
  filter_upwards [eventually_raw_radius_moment_bound n gaps hgaps (2*k)] with a hb
  have he (v : FreeVector (n+1)) : (ENNReal.ofReal C*ENNReal.ofReal (radius v^k))^2 =
      ENNReal.ofReal (C^2)*ENNReal.ofReal (radius v^(2*k)) := by
    rw [mul_pow,← ENNReal.ofReal_pow hC,← ENNReal.ofReal_pow (pow_nonneg (zero_le_one.trans (one_le_radius v)) k)]
    rw [← pow_mul,mul_comm k 2]
  calc
    _ ≤ ∫⁻ v, rawMultiDensity n a gaps v*(ENNReal.ofReal (C^2)*ENNReal.ofReal (radius v^(2*k))) := by
      apply lintegral_mono
      intro v
      exact mul_le_mul' le_rfl (by rw [← he]; exact pow_le_pow_left₀ (show 0 ≤ Ψ v from zero_le) (hbound v) 2)
    _ = ENNReal.ofReal (C^2)*(∫⁻ v, rawMultiDensity n a gaps v*ENNReal.ofReal (radius v^(2*k))) := by
      simp_rw [show ∀ v : FreeVector (n+1), rawMultiDensity n a gaps v*(ENNReal.ofReal (C^2)*ENNReal.ofReal (radius v^(2*k))) =
        ENNReal.ofReal (C^2)*(rawMultiDensity n a gaps v*ENNReal.ofReal (radius v^(2*k))) by intro v; ac_rfl]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl hb

theorem overlap_growth_test_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (k : ℕ)
    (Ψ : FreeVector (n+1) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C*ENNReal.ofReal (radius v^k)) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v, overlap n a gaps v*Ψ v) (𝓝[>] 0)
      (𝓝 (∫⁻ v, entranceProduct n gaps v*Ψ v)) := by
  have hfin : (∫⁻ v, entranceProduct n gaps v*Ψ v) ≠ ∞ := by
    have he := entrance_growth_test_lt_top n gaps hgaps C k Ψ hbound
    rw [entranceLaw,lintegral_withDensity_eq_lintegral_mul volume (measurable_entranceProduct n gaps) hΨ] at he
    exact he.ne
  have hp : ∀ᵐ v ∂volume, Tendsto (fun a : ℝ ↦ overlap n a gaps v*Ψ v) (𝓝[>] 0)
      (𝓝 (entranceProduct n gaps v*Ψ v)) := by
    apply ae_of_all
    intro v
    have hΨfin : Ψ v ≠ ∞ := ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hbound v)
    have he : Tendsto (fun a : ℝ ↦ overlap n a gaps v) (𝓝[>] 0) (𝓝 (entranceProduct n gaps v)) := by
      simpa only [overlap,min_self] using
        (rawMultiDensity_tendsto n gaps (hgaps 0 (by omega)) (hgaps (n+1) (by omega))
          (positive_finalTime n gaps hgaps) v).min (tendsto_const_nhds (x := entranceProduct n gaps v))
    exact ENNReal.Tendsto.mul_const he (Or.inr hΨfin)
  exact tendsto_lintegral_filter_of_dominated_convergence
    (fun v ↦ entranceProduct n gaps v*Ψ v)
    (Eventually.of_forall (fun a ↦ (measurable_overlap n a gaps).mul hΨ))
    (Eventually.of_forall (fun _ ↦ ae_of_all _ (fun v ↦ mul_le_mul' (min_le_right _ _) le_rfl))) hfin hp

theorem growth_density_remainder_tendsto_zero (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (Ψ : FreeVector (n+1) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C*ENNReal.ofReal (radius v^k)) :
    Tendsto (fun a : ℝ ↦ ∫⁻ v, (rawMultiDensity n a gaps v-overlap n a gaps v)*Ψ v)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  let M := ENNReal.ofReal (C^2)*jointMomentBound (sampleTime gaps (n+2)) (n+1) (2*k)
  have hM : M ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (jointMomentBound_lt_top _ (positive_finalTime n gaps hgaps) _ _).ne
  have ht := ENNReal.Tendsto.mul_const
    ((density_remainder_integral_tendsto_zero n gaps hgaps).ennrpow_const (1/2))
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (y := (1/2 : ℝ)) (by norm_num) hM))
  have hu : Tendsto (fun a : ℝ ↦ (∫⁻ v, rawMultiDensity n a gaps v-overlap n a gaps v)^(1/2 : ℝ)*M^(1/2 : ℝ))
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by simpa using ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun _ ↦ zero_le)
  · filter_upwards [eventually_raw_growth_test_square_bound n gaps hgaps C hC k Ψ hbound] with a hb
    have hd := (measurable_rawMultiDensity n a gaps).sub (measurable_overlap n a gaps)
    calc
      _ ≤ (∫⁻ v, rawMultiDensity n a gaps v-overlap n a gaps v)^(1/2 : ℝ)*
          (∫⁻ v, (rawMultiDensity n a gaps v-overlap n a gaps v)*(Ψ v)^2)^(1/2 : ℝ) :=
        weighted_lintegral_le_half_moments volume hd hΨ
      _ ≤ _ := mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (by
          calc
            _ ≤ ∫⁻ v, rawMultiDensity n a gaps v*(Ψ v)^2 :=
              lintegral_mono (fun v ↦ mul_le_mul' tsub_le_self le_rfl)
            _ ≤ M := hb) (by norm_num))

theorem actual_growth_test_lintegral_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (Ψ : FreeVector (n+1) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C*ENNReal.ofReal (radius v^k)) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g : Path, Ψ (internalEval (n+1) gaps g)
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫⁻ v, Ψ v ∂entranceLaw n gaps)) := by
  have ht := (overlap_growth_test_tendsto n gaps hgaps C k Ψ hΨ hbound).add
    (growth_density_remainder_tendsto_zero n gaps hgaps C hC k Ψ hΨ hbound)
  simp only [add_zero] at ht
  rw [entranceLaw,lintegral_withDensity_eq_lintegral_mul volume (measurable_entranceProduct n gaps) hΨ]
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [multiPoint_lintegral (n+1) a ha gaps (fun j hj ↦ hgaps j (by omega))
    (hgaps (n+1) (by omega)) Ψ hΨ]
  have hm : Measurable (fun v : FreeVector (n+1) ↦ overlap n a gaps v*Ψ v) :=
    (measurable_overlap n a gaps).mul hΨ
  rw [← lintegral_add_left hm]
  apply lintegral_congr
  intro v
  have hv : overlap n a gaps v ≤ rawMultiDensity n a gaps v := min_le_left _ _
  rw [← add_mul,add_tsub_cancel_of_le hv]
  rfl

theorem entrance_growth_real_test_integrable (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (Φ : FreeVector (n+1) → ℝ) (hΦ : Measurable Φ)
    (hbound : ∀ v, |Φ v| ≤ C*radius v^k) : Integrable Φ (entranceLaw n gaps) := by
  refine ⟨hΦ.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_norm Φ).mpr
  simp only [Real.norm_eq_abs]
  apply entrance_growth_test_lt_top n gaps hgaps C k (fun v ↦ ENNReal.ofReal |Φ v|)
  intro v
  calc
    _ ≤ ENNReal.ofReal (C*radius v^k) := ENNReal.ofReal_le_ofReal (hbound v)
    _ = _ := ENNReal.ofReal_mul hC

theorem eventually_actual_growth_real_test_integrable (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (Φ : FreeVector (n+1) → ℝ) (hΦ : Measurable Φ)
    (hbound : ∀ v, |Φ v| ≤ C*radius v^k) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, Integrable (fun g : Path ↦ Φ (internalEval (n+1) gaps g))
      (positiveBridgeLaw a (sampleTime gaps (n+2))) := by
  filter_upwards [self_mem_nhdsWithin,eventually_raw_radius_moment_bound n gaps hgaps k] with a ha hb
  have hm : Measurable (fun g : Path ↦ Φ (internalEval (n+1) gaps g)) :=
    hΦ.comp (continuous_internalEval _ _).measurable
  refine ⟨hm.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_norm _).mpr
  simp only [Real.norm_eq_abs]
  rw [multiPoint_lintegral (n+1) a ha gaps (fun j hj ↦ hgaps j (by omega))
    (hgaps (n+1) (by omega)) (fun v ↦ ENNReal.ofReal |Φ v|) hΦ.abs.ennreal_ofReal]
  have he : (∫⁻ v, rawMultiDensity n a gaps v*ENNReal.ofReal |Φ v|) ≤
      ENNReal.ofReal C*jointMomentBound (sampleTime gaps (n+2)) (n+1) k := by
    calc
      _ ≤ ∫⁻ v, rawMultiDensity n a gaps v*(ENNReal.ofReal C*ENNReal.ofReal (radius v^k)) := by
        apply lintegral_mono
        intro v
        apply mul_le_mul' le_rfl
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hbound v)
      _ = ENNReal.ofReal C*(∫⁻ v, rawMultiDensity n a gaps v*ENNReal.ofReal (radius v^k)) := by
        simp_rw [show ∀ v : FreeVector (n+1), rawMultiDensity n a gaps v*(ENNReal.ofReal C*ENNReal.ofReal (radius v^k)) =
          ENNReal.ofReal C*(rawMultiDensity n a gaps v*ENNReal.ofReal (radius v^k)) by intro v; ac_rfl]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl hb
  exact he.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (jointMomentBound_lt_top _ (positive_finalTime n gaps hgaps) _ _))

theorem actual_growth_real_test_integral_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (Φ : FreeVector (n+1) → ℝ) (hΦ : Measurable Φ)
    (hbound : ∀ v, |Φ v| ≤ C*radius v^k) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, Φ (internalEval (n+1) gaps g)
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫ v, Φ v ∂entranceLaw n gaps)) := by
  have hp (v : FreeVector (n+1)) : ENNReal.ofReal (Φ v) ≤ ENNReal.ofReal C*ENNReal.ofReal (radius v^k) := by
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hbound v))
  have hn (v : FreeVector (n+1)) : ENNReal.ofReal (-Φ v) ≤ ENNReal.ofReal C*ENNReal.ofReal (radius v^k) := by
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hbound v))
  have hpl := actual_growth_test_lintegral_tendsto n gaps hgaps C hC k _ hΦ.ennreal_ofReal hp
  have hnl := actual_growth_test_lintegral_tendsto n gaps hgaps C hC k _ hΦ.neg.ennreal_ofReal hn
  have hpf := (entrance_growth_test_lt_top n gaps hgaps C k _ hp).ne
  have hnf := (entrance_growth_test_lt_top n gaps hgaps C k _ hn).ne
  have he := ((ENNReal.tendsto_toReal hpf).comp hpl).sub ((ENNReal.tendsto_toReal hnf).comp hnl)
  rw [← integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (entrance_growth_real_test_integrable n gaps hgaps C hC k Φ hΦ hbound)] at he
  apply he.congr'
  filter_upwards [eventually_actual_growth_real_test_integrable n gaps hgaps C hC k Φ hΦ hbound] with a ha
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part ha).symm

theorem actual_monomial_integral_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (p : Fin (n+1) → ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, monomial p (internalEval (n+1) gaps g)
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫ v, monomial p v ∂entranceLaw n gaps)) := by
  apply actual_growth_real_test_integral_tendsto n gaps hgaps 1 (by norm_num)
    (∑ i, p i) (monomial p) (continuous_monomial p).measurable
  intro v
  simpa only [one_mul] using abs_monomial_le_radius_pow p v

theorem actual_coordinatePolynomial_integral_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (m : ℕ) (c : Fin m → ℝ)
    (p : Fin m → Fin (n+1) → ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, coordinatePolynomial c p (internalEval (n+1) gaps g)
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫ v, coordinatePolynomial c p v ∂entranceLaw n gaps)) :=
  actual_growth_real_test_integral_tendsto n gaps hgaps (∑ j, |c j|)
    (Finset.sum_nonneg (fun j _ ↦ abs_nonneg (c j))) (∑ j, ∑ i, p j i)
    (coordinatePolynomial c p) (continuous_coordinatePolynomial c p).measurable
    (abs_coordinatePolynomial_le_radius_pow c p)

theorem actual_height_product_integral_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, (∏ i : Fin (n+1), g (internalTimes (n+1) gaps i))
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫ v : FreeVector (n+1), (∏ i, v i) ∂entranceLaw n gaps)) := by
  simpa only [monomial,pow_one,internalEval] using
    actual_monomial_integral_tendsto n gaps hgaps (fun _ ↦ 1)

theorem actual_ordered_coordinatePolynomial_integral_tendsto (n : ℕ)
    (times : Fin (n+3) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (m : ℕ) (c : Fin m → ℝ) (p : Fin m → Fin (n+1) → ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, coordinatePolynomial c p
        (fun i : Fin (n+1) ↦ g (times i.succ.castSucc))
        ∂positiveBridgeLaw a (times (Fin.last (n+2)))) (𝓝[>] 0)
      (𝓝 (∫ v : FreeVector (n+1), coordinatePolynomial c p v
        ∂entranceLaw n (orderedGaps (n+2) times))) := by
  have hgaps : ∀ j < n+2, 0 < orderedGaps (n+2) times j :=
    fun j hj ↦ orderedGaps_positive (n+2) times hstrict j hj
  have he := actual_coordinatePolynomial_integral_tendsto n (orderedGaps (n+2) times) hgaps m c p
  have hT := sampleTime_orderedGaps (n+2) times hstrict.monotone hzero (Fin.last (n+2))
  simp only [Fin.val_last] at hT
  rw [hT,internalEval_orderedGaps (n+1) times hstrict.monotone hzero] at he
  exact he

theorem actual_absolute_monomial_moment_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (p : Fin (n+1) → ℕ) (l : ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, |monomial p (internalEval (n+1) gaps g)|^l
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫ v, |monomial p v|^l ∂entranceLaw n gaps)) := by
  apply actual_growth_real_test_integral_tendsto n gaps hgaps 1 (by norm_num)
    ((∑ i, p i)*l) (fun v ↦ |monomial p v|^l) ((continuous_monomial p).abs.pow l).measurable
  intro v
  rw [abs_of_nonneg (by positivity),one_mul]
  exact abs_monomial_pow_le_radius_pow p v l

theorem actual_coordinatePolynomial_power_integral_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (m : ℕ) (c : Fin m → ℝ)
    (p : Fin m → Fin (n+1) → ℕ) (l : ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, (coordinatePolynomial c p (internalEval (n+1) gaps g))^l
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫ v, (coordinatePolynomial c p v)^l ∂entranceLaw n gaps)) := by
  have hC : 0 ≤ ∑ j, |c j| := Finset.sum_nonneg (fun j _ ↦ abs_nonneg (c j))
  apply actual_growth_real_test_integral_tendsto n gaps hgaps ((∑ j, |c j|)^l)
    (pow_nonneg hC l) ((∑ j, ∑ i, p j i)*l) (fun v ↦ (coordinatePolynomial c p v)^l)
    ((continuous_coordinatePolynomial c p).pow l).measurable
  intro v
  rw [abs_pow]
  calc
    _ ≤ ((∑ j, |c j|)*radius v^(∑ j, ∑ i, p j i))^l :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_coordinatePolynomial_le_radius_pow c p v) l
    _ = _ := by rw [mul_pow,← pow_mul]

theorem actual_radius_moment_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (k : ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, radius (internalEval (n+1) gaps g)^k
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫ v : FreeVector (n+1), radius v^k ∂entranceLaw n gaps)) := by
  apply actual_growth_real_test_integral_tendsto n gaps hgaps 1 (by norm_num) k
    (fun v ↦ radius v^k) ((continuous_radius _).pow k).measurable
  intro v
  rw [abs_of_nonneg (pow_nonneg (zero_le_one.trans (one_le_radius v)) k),one_mul]

theorem actual_sum_abs_moment_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (k : ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, (∑ i : Fin (n+1), |g (internalTimes (n+1) gaps i)|)^k
        ∂positiveBridgeLaw a (sampleTime gaps (n+2))) (𝓝[>] 0)
      (𝓝 (∫ v : FreeVector (n+1), (∑ i, |v i|)^k ∂entranceLaw n gaps)) := by
  have hm : Continuous (fun v : FreeVector (n+1) ↦ (∑ i, |v i|)^k) :=
    (continuous_finsetSum _ (fun i _ ↦ (continuous_apply i).abs)).pow k
  have hb (v : FreeVector (n+1)) : |(∑ i, |v i|)^k| ≤ 1*radius v^k := by
    rw [abs_of_nonneg (pow_nonneg (Finset.sum_nonneg (fun i _ ↦ abs_nonneg (v i))) k),one_mul]
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ ↦ abs_nonneg (v i)))
    exact le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [internalEval] using actual_growth_real_test_integral_tendsto n gaps hgaps
    1 (by norm_num) k _ hm.measurable hb

end PerronWright.BrownianPositiveBridgeJointMomentLimits
