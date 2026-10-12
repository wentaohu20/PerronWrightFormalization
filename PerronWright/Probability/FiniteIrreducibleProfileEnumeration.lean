import PerronWright.Analysis.FiniteIrreducibleFieldTreeConnectedWeightAsymptotic
import PerronWright.Analysis.FiniteIrreducibleFieldUnicyclicCoefficientAsymptotic
import PerronWright.Analysis.FiniteIrreducibleConnectedFieldAsymptotic
import PerronWright.Analysis.FieldLogRadiusTaylor

/-!
# Complete uniform general-field connected enumeration for profile bounds

The tree, unicyclic, cubic, and noncubic coefficient theorems are assembled
for the literal connected enumerator. The positive-surplus assertion includes
both core classes. A finite surplus cutoff is handled by finite induction.
-/

open Filter Topology Asymptotics
open scoped Classical Topology Real

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.FiniteIrreducibleProfileEnumeration

open GraphCore

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- One comparison main term for each surplus. For surplus one we use its
exact factorial logarithmic coefficient, avoiding an unnecessary Stirling
conversion in the profile ratio. -/
def mainTerm (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (k : ℕ) : ℕ → ℂ
  | 0 => (FiniteIrreducibleFieldTreeConnectedWeightAsymptotic.fieldTreePerronWrightMainTerm M hM k : ℂ)
  | 1 => (k.factorial : ℂ) * ((1 / 4 : ℂ) * (k : ℂ)⁻¹)
  | ell + 2 => (Real.sqrt (M.beta hM) : ℂ) ^ (ell + 1) *
      positiveSurplusCubicFactorialMain (ell + 1) k

/-- The genuine total cubic-plus-noncubic positive-surplus estimate. -/
theorem exists_positiveSurplus_local_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ g : C(S, ℂ), ‖g‖ ≤ ε →
        ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
            M.bjrModel.complexFieldConnectedWeight g k (ell + 1) /
            ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
              positiveSurplusCubicFactorialMain ell k) - 1‖ ≤
          C * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
  FiniteIrreducibleConnectedFieldAsymptotic.exists_complexFieldConnectedWeight_local_relative_bound
    M hM hell

/-- Uniform unicyclic relative error compared with the exact factorial
logarithmic main term. -/
theorem exists_unicyclic_local_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ g : C(S, ℂ), ‖g‖ ≤ ε →
        ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k * M.bjrModel.complexFieldConnectedWeight g k 1 /
            mainTerm M hM k 1 - 1‖ ≤
          C * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨s, K, N, hs, hK, hbound⟩ :=
    FiniteIrreducibleFieldUnicyclicCoefficientAsymptotic.exists_complexFieldUnicyclic_connectedWeight_uniform_bound M hM
  refine ⟨s / 2, 4 * K, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (1 : ℕ)] with k hk hk1
  intro g hg
  have hgs : g ∈ Metric.ball (0 : C(S, ℂ)) s := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_one.trans_le hk1)
  have hkcomplex : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_one.trans_le hk1).ne'
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  let q : ℂ := (1 / 4 : ℂ) * (k : ℂ)⁻¹
  have hq : q ≠ 0 := mul_ne_zero (by norm_num) (inv_ne_zero hkcomplex)
  have heq : (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k * M.bjrModel.complexFieldConnectedWeight g k 1 /
      mainTerm M hM k 1 - 1 =
      ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
        (M.bjrModel.complexFieldConnectedWeight g k 1 / (k.factorial : ℂ)) - q) / q := by
    simp only [mainTerm]
    dsimp only [q]
    field_simp [hf, hkcomplex]
  rw [heq, norm_div]
  have hqnorm : ‖q‖ = (4 * (k : ℝ))⁻¹ := by
    dsimp only [q]
    rw [norm_mul, norm_div, norm_inv, Complex.norm_natCast]
    norm_num
    ring
  rw [hqnorm, div_inv_eq_mul]
  have hpow : (k : ℝ) ^ (-(3 / 2 : ℝ)) * (k : ℝ) =
      (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    nth_rw 2 [← Real.rpow_one (k : ℝ)]
    rw [← Real.rpow_add hkreal]
    norm_num
  calc
    ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
        (M.bjrModel.complexFieldConnectedWeight g k 1 / (k.factorial : ℂ)) - q‖ * (4 * (k : ℝ)) ≤
        (K * (k : ℝ) ^ (-(3 / 2 : ℝ))) * (4 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_right (hbound g hgs k hk) (by positivity)
    _ = (4 * K) * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc]; nlinarith [hpow]
    _ ≤ _ := by nlinarith [norm_nonneg g, hK]

/-- Local normalized connected-weight asymptotics for every fixed surplus
and every small continuous complex field. -/
theorem exists_local_relative_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (r : ℕ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ g : C(S, ℂ), ‖g‖ ≤ ε →
        ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k * M.bjrModel.complexFieldConnectedWeight g k r /
            mainTerm M hM k r - 1‖ ≤
          C * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  cases r with
  | zero =>
    simpa only [mainTerm] using
      FiniteIrreducibleFieldTreeConnectedWeightAsymptotic.exists_complexFieldConnectedWeight_perronWright_local_relative_bound M hM
  | succ r =>
    cases r with
    | zero => exact exists_unicyclic_local_relative_bound M hM
    | succ ell =>
      simpa only [mainTerm, Nat.add_assoc] using
        exists_positiveSurplus_local_relative_bound M hM (Nat.succ_pos ell)

/-- Genuine finite-cutoff uniformity: both the field ball and the error
constant are chosen before the surplus, size, and arbitrary Banach field. -/
theorem exists_boundedSurplus_local_relative_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℂ), ‖g‖ ≤ ε →
        ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k * M.bjrModel.complexFieldConnectedWeight g k r /
            mainTerm M hM k r - 1‖ ≤
          C * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  induction R with
  | zero =>
    obtain ⟨ε, C, hε, hC, hbound⟩ := exists_local_relative_bound M hM 0
    refine ⟨ε, C, hε, hC, ?_⟩
    filter_upwards [hbound] with k hk
    intro r hr g hg
    have hr0 : r = 0 := by omega
    subst r
    exact hk g hg
  | succ R ih =>
    obtain ⟨ε₁, C₁, hε₁, hC₁, hbound₁⟩ := ih
    obtain ⟨ε₂, C₂, hε₂, hC₂, hbound₂⟩ := exists_local_relative_bound M hM (R + 1)
    refine ⟨min ε₁ ε₂, C₁ + C₂, lt_min hε₁ hε₂, add_pos hC₁ hC₂, ?_⟩
    filter_upwards [hbound₁, hbound₂] with k hk₁ hk₂
    intro r hr g hg
    have hscale : 0 ≤ ‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
      add_nonneg (norm_nonneg g) (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    by_cases hrtop : r = R + 1
    · subst r
      exact (hk₂ g (hg.trans (min_le_right _ _))).trans
        (mul_le_mul_of_nonneg_right (by linarith) hscale)
    · exact (hk₁ r (by omega) g (hg.trans (min_le_left _ _))).trans
        (mul_le_mul_of_nonneg_right (by linarith) hscale)

/-- On a smaller genuine field ball, all the normalized connected
enumerators are uniformly separated from zero and bounded above. -/
theorem exists_boundedSurplus_normalized_bounds (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℂ), ‖g‖ ≤ ε →
        (1 / 2 : ℝ) ≤ ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
          M.bjrModel.complexFieldConnectedWeight g k r / mainTerm M hM k r‖ ∧
        ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
          M.bjrModel.complexFieldConnectedWeight g k r / mainTerm M hM k r‖ ≤ 3 / 2 := by
  obtain ⟨ε₀, C, hε₀, hC, hbound⟩ := exists_boundedSurplus_local_relative_bound M hM R
  let ε : ℝ := min ε₀ (1 / (4 * C))
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hhalf : Tendsto (fun k : ℕ ↦ C * (k : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hbound, hhalf.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
    with k hk hkhalf
  intro r hr g hg
  have hεC : C * ε ≤ 1 / 4 := by
    have he := min_le_right ε₀ (1 / (4 * C))
    have hmul := mul_le_mul_of_nonneg_left he hC.le
    have hc : C * (1 / (4 * C)) = 1 / 4 := by field_simp [hC.ne']
    simpa only [ε, hc] using hmul
  have he := hk r hr g (hg.trans (min_le_left _ _))
  have herr : ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
      M.bjrModel.complexFieldConnectedWeight g k r / mainTerm M hM k r - 1‖ ≤ 1 / 2 := by
    refine he.trans ?_
    have hgC := (mul_le_mul_of_nonneg_left hg hC.le).trans hεC
    rw [mul_add]
    linarith
  have hu := norm_sub_norm_le ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
      M.bjrModel.complexFieldConnectedWeight g k r / mainTerm M hM k r) 1
  have hl := norm_sub_norm_le (1 : ℂ) ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
      M.bjrModel.complexFieldConnectedWeight g k r / mainTerm M hM k r)
  rw [norm_sub_rev] at hl
  norm_num only [norm_one] at hu hl
  constructor <;> linarith

/-- Uniform normalized enumerator ratio control for two arbitrary fields
in one genuine field ball, with all surpluses up to `R` covered. -/
theorem exists_boundedSurplus_normalized_ratio_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ g h : C(S, ℂ), ‖g‖ ≤ ε → ‖h‖ ≤ ε →
        ‖((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k * M.bjrModel.complexFieldConnectedWeight g k r) /
          ((FiniteIrreducibleRadiusResponse.radius M hM h) ^ k * M.bjrModel.complexFieldConnectedWeight h k r)‖ ≤ 3 := by
  obtain ⟨ε, hε, hbound⟩ := exists_boundedSurplus_normalized_bounds M hM R
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hbound] with k hk
  intro r hr g h hg hh
  have hgb := hk r hr g hg
  have hhb := hk r hr h hh
  let P : ℂ := mainTerm M hM k r
  let G : ℂ := (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k * M.bjrModel.complexFieldConnectedWeight g k r
  let H : ℂ := (FiniteIrreducibleRadiusResponse.radius M hM h) ^ k * M.bjrModel.complexFieldConnectedWeight h k r
  have hHB : (0 : ℝ) < ‖H / P‖ := lt_of_lt_of_le (by norm_num) hhb.1
  have hHdiv : H / P ≠ 0 := norm_pos_iff.mp hHB
  have hP : P ≠ 0 := by
    intro hzero
    exact hHdiv (by rw [hzero, div_zero])
  have hH : H ≠ 0 := by
    intro hzero
    exact hHdiv (by rw [hzero, zero_div])
  have heq : G / H = (G / P) / (H / P) := by field_simp [hP, hH]
  change ‖G / H‖ ≤ 3
  rw [heq, norm_div]
  apply (div_le_iff₀ hHB).mpr
  dsimp only [G, H, P] at *
  linarith [hgb.2, hhb.1]

end PerronWright.FiniteIrreducibleProfileEnumeration


