import PerronWright.Probability.BrownianDyadicModulus
import PerronWright.Probability.DyadicGeometricExtension

/-! # A proved dyadic regularity mechanism for genuine finite path laws

Only measurable sampled coordinates and their fourth-moment inequalities
are inputs. Markov, finite unions, geometric summation and Borel--Cantelli
produce the almost-sure neighbor bounds required by the existing literal
dyadic extension. No continuity or regularity conclusion is a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FourthMomentDyadicModulus

open BrownianDyadicModulus DyadicGeometricApproximation DyadicGeometricExtension

variable {Ω : Type*} [MeasurableSpace Ω]

def increment (a : ℕ → ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ := a n (k+1) ω-a n k ω

def badLevel (a : ℕ → ℕ → Ω → ℝ) (M n : ℕ) (R : ℝ) : Set Ω :=
  ⋃ k : Fin (M*2^n), {ω | R*decay^n ≤ ‖increment a n k.val ω‖}

theorem measurable_increment (a : ℕ → ℕ → Ω → ℝ) (ha : ∀ n k, Measurable (a n k)) (n k : ℕ) :
    Measurable (increment a n k) := (ha n (k+1)).sub (ha n k)

theorem measurableSet_badLevel (a : ℕ → ℕ → Ω → ℝ) (ha : ∀ n k, Measurable (a n k))
    (M n : ℕ) (R : ℝ) : MeasurableSet (badLevel a M n R) := by
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_le measurable_const (measurable_increment a ha n k.val).norm

variable (μ : Measure Ω) [IsFiniteMeasure μ]
variable (a : ℕ → ℕ → Ω → ℝ) (ha : ∀ n k, Measurable (a n k))
variable (C : ℝ) (hC : 0 ≤ C)
variable (h4 : ∀ n k, (∫⁻ ω, ENNReal.ofReal (‖increment a n k ω‖^4) ∂μ) ≤
  ENNReal.ofReal (C*(1/(2 : ℝ)^n)^2))

include ha hC h4

omit [IsFiniteMeasure μ] in
theorem increment_tail_bound (n k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ ‖increment a n k ω‖} ≤ C*(1/(2 : ℝ)^n)^2/ε^4 := by
  have hpow : 0 < ε^4 := pow_pos hε 4
  have hmeas : Measurable (fun ω ↦ ENNReal.ofReal (‖increment a n k ω‖^4)) :=
    ((measurable_increment a ha n k).norm.pow_const 4).ennreal_ofReal
  have hb : μ {ω | ε ≤ ‖increment a n k ω‖} ≤ ENNReal.ofReal (C*(1/(2 : ℝ)^n)^2/ε^4) := by
    calc
      _ ≤ μ {ω | ENNReal.ofReal (ε^4) ≤ ENNReal.ofReal (‖increment a n k ω‖^4)} := by
        apply measure_mono
        intro ω hω
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hω 4)
      _ ≤ (∫⁻ ω, ENNReal.ofReal (‖increment a n k ω‖^4) ∂μ)/ENNReal.ofReal (ε^4) :=
        meas_ge_le_lintegral_div hmeas.aemeasurable
          (ENNReal.ofReal_ne_zero_iff.mpr hpow) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C*(1/(2 : ℝ)^n)^2)/ENNReal.ofReal (ε^4) :=
        ENNReal.div_le_div_right (h4 n k) _
      _ = _ := (ENNReal.ofReal_div_of_pos hpow).symm
  calc
    _ ≤ (ENNReal.ofReal (C*(1/(2 : ℝ)^n)^2/ε^4)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    _ = _ := ENNReal.toReal_ofReal (div_nonneg (mul_nonneg hC (sq_nonneg _)) hpow.le)

omit ha hC h4 in
theorem scaled_tail_algebra (M n : ℕ) {R : ℝ} (hR : 0 < R) :
    (M*2^n : ℕ)*(C*(1/(2 : ℝ)^n)^2/(R*decay^n)^4) =
      (C*(M : ℝ)/R^4)*tailRatio^n := by
  have hd : decay ≠ 0 := ne_of_gt decay_pos
  have hr : R ≠ 0 := ne_of_gt hR
  have hp : (decay^4)^n = (decay^n)^4 := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,tailRatio,div_pow,one_pow,mul_pow,hp]
  field_simp

omit [IsFiniteMeasure μ] in
theorem badLevel_real_bound (M n : ℕ) {R : ℝ} (hR : 0 < R) :
    μ.real (badLevel a M n R) ≤ (C*(M : ℝ)/R^4)*tailRatio^n := by
  calc
    _ ≤ ∑ k : Fin (M*2^n), μ.real {ω | R*decay^n ≤ ‖increment a n k.val ω‖} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin (M*2^n), C*(1/(2 : ℝ)^n)^2/(R*decay^n)^4 :=
      Finset.sum_le_sum (fun k _ ↦ increment_tail_bound μ a ha C hC h4 n k.val (mul_pos hR (pow_pos decay_pos n)))
    _ = _ := by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        scaled_tail_algebra C M n hR

theorem badLevel_measure_bound (M n : ℕ) {R : ℝ} (hR : 0 < R) :
    μ (badLevel a M n R) ≤ ENNReal.ofReal ((C*(M : ℝ)/R^4)*tailRatio^n) := by
  calc
    _ = ENNReal.ofReal (μ.real (badLevel a M n R)) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (badLevel_real_bound μ a ha C hC h4 M n hR)

theorem badLevel_tsum_ne_top (M : ℕ) {R : ℝ} (hR : 0 < R) :
    (∑' n, μ (badLevel a M n R)) ≠ ∞ := by
  have hs : Summable (fun n : ℕ ↦ (C*(M : ℝ)/R^4)*tailRatio^n) :=
    (summable_geometric_of_abs_lt_one (by rw [abs_of_pos tailRatio_pos]; exact tailRatio_lt_one)).mul_left _
  exact ne_of_lt ((ENNReal.tsum_le_tsum (fun n ↦ badLevel_measure_bound μ a ha C hC h4 M n hR)).trans_lt
    hs.tsum_ofReal_lt_top)

theorem allLevel_bad_measure_bound (M : ℕ) {R : ℝ} (hR : 0 < R) :
    μ (⋃ n, badLevel a M n R) ≤
      ENNReal.ofReal ((C*(M : ℝ)/R^4)/(1-tailRatio)) := by
  have hq : |tailRatio| < 1 := by
    rw [abs_of_pos tailRatio_pos]
    exact tailRatio_lt_one
  have hs : Summable (fun n : ℕ ↦ tailRatio^n) := summable_geometric_of_abs_lt_one hq
  have hnonneg : ∀ n : ℕ, 0 ≤ (C*(M : ℝ)/R^4)*tailRatio^n := fun n ↦
    mul_nonneg (div_nonneg (mul_nonneg hC (Nat.cast_nonneg M)) (pow_nonneg hR.le 4))
      (pow_nonneg tailRatio_pos.le n)
  calc
    _ ≤ ∑' n, μ (badLevel a M n R) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal ((C*(M : ℝ)/R^4)*tailRatio^n) :=
      ENNReal.tsum_le_tsum (fun n ↦ badLevel_measure_bound μ a ha C hC h4 M n hR)
    _ = ENNReal.ofReal (∑' n : ℕ, (C*(M : ℝ)/R^4)*tailRatio^n) :=
      (ENNReal.ofReal_tsum_of_nonneg hnonneg (hs.mul_left _)).symm
    _ = _ := by
      rw [hs.tsum_mul_left,tsum_geometric_of_abs_lt_one hq]
      simp only [div_eq_mul_inv]

theorem ae_eventually_neighbor_bound (M : ℕ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ k : ℕ, k < M*2^n → ‖increment a n k ω‖ ≤ decay^n := by
  filter_upwards [ae_eventually_notMem (badLevel_tsum_ne_top μ a ha C hC h4 M (by norm_num : (0 : ℝ) < 1))]
    with ω hω
  filter_upwards [hω] with n hn
  intro k hk
  have hnot : ¬decay^n ≤ ‖increment a n k ω‖ := by
    intro he
    exact hn (mem_iUnion.mpr ⟨⟨k,hk⟩,by
      change 1*decay^n ≤ ‖increment a n k ω‖
      simpa only [one_mul] using he⟩)
  exact (lt_of_not_ge hnot).le

theorem ae_localBound : ∀ᵐ ω ∂μ, LocalBound (fun n k ↦ a n k ω) := by
  have hh : ∀ᵐ ω ∂μ, ∀ M : ℕ, ∀ᶠ n in atTop, ∀ k : ℕ,
      k < M*2^n → ‖increment a n k ω‖ ≤ decay^n :=
    ae_all_iff.mpr (fun M ↦ ae_eventually_neighbor_bound μ a ha C hC h4 M)
  filter_upwards [hh] with ω hω
  intro M
  simpa only [increment,decay,ratio] using
    BrownianDyadicModulus.exists_all_level_constant (fun n k ↦ increment a n k ω) M (hω M)

theorem ae_continuous_extension (hc : ∀ ω, Compatible (fun n k ↦ a n k ω)) :
    ∀ᵐ ω ∂μ, Continuous (extension (fun n k ↦ a n k ω)) := by
  filter_upwards [ae_localBound μ a ha C hC h4] with ω hω
  exact continuous_extension (hc ω) hω

theorem ae_all_samples_match_extension (hc : ∀ ω, Compatible (fun n k ↦ a n k ω)) :
    ∀ᵐ ω ∂μ, ∀ n k, extension (fun n k ↦ a n k ω) (DyadicFloorGeometry.coordinate n k) = a n k ω := by
  filter_upwards [ae_localBound μ a ha C hC h4] with ω hω
  exact extension_dyadic (hc ω) hω

end PerronWright.FourthMomentDyadicModulus
