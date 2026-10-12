import PerronWright.Probability.ProfileSquareSeries
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Actual finite products of connected component profile laws

Small component sizes are controlled deterministically; large component
sizes use the proved field enumeration bound. The joint law below is the
literal finite product, not an interface assumption.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.ProfileFiniteCollection

open ConnectedTypeLaw ProfileLaplace ProfileSquareMoment ProfileSquareSeries

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Fixed linear tilts are uniformly bounded for every positive component
size, including the finite initial range. -/
theorem exists_all_size_scaled_laplace_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    ∃ B : ℝ, 0 < B ∧ ∀ k : ℕ, 0 < k → ∀ r : ℕ, r ≤ R →
      ∀ g f : C(S, ℝ), Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ‖f‖ ≤ 1 →
      ∀ u : ℝ, |u| ≤ U → ∀ hC : 0 < M.fieldConnectedWeight g k r,
      (∫ p, Real.exp (u * scaledSum M hM f p) ∂law M g k r hC) ≤ B := by
  obtain ⟨B₀, hB₀, hlarge⟩ := exists_uniform_scaled_laplace_bound M hM R L U hL hU
  obtain ⟨K, hK⟩ := eventually_atTop.mp hlarge
  let B : ℝ := 2 * B₀ + Real.exp (2 * U * Real.sqrt (K : ℝ))
  refine ⟨B, by dsimp only [B]; positivity, ?_⟩
  intro k hk r hr g f hg hf u hu hC
  have hunit (p : State S k) : |scaledSum M hM f p| ≤ 2 * Real.sqrt (k : ℝ) := by
    exact (scaledSum_abs_le M hM hk f p).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2 * Real.sqrt (k : ℝ))])
  have hm (v : ℝ) : Measurable (fun p : State S k ↦ Real.exp (v * scaledSum M hM f p)) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul (scaledSum_measurable M hM f))
  have hi (v : ℝ) : Integrable (fun p : State S k ↦ Real.exp (v * scaledSum M hM f p))
      (law M g k r hC) := by
    apply integrable_of_measurable_abs_le (law M g k r hC) (hm v)
      (B := Real.exp (|v| * (2 * Real.sqrt (k : ℝ))))
    intro p
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |v * scaledSum M hM f p| := le_abs_self _
      _ = |v| * |scaledSum M hM f p| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hunit p) (abs_nonneg _)
  by_cases hkK : K ≤ k
  · have hb := (hK k hkK).2 r hr g f hg hf hC
    have hn := (hK k hkK).2 r hr g (-f) hg (by simpa only [norm_neg] using hf) hC
    simp_rw [scaledSum_neg, mul_neg, ← neg_mul] at hn
    have hpoint (p : State S k) : Real.exp (u * scaledSum M hM f p) ≤
        Real.exp (U * scaledSum M hM f p) + Real.exp (-U * scaledSum M hM f p) := by
      apply (Real.exp_le_exp.mpr ?_).trans (exp_abs_le_exp_add_exp_neg U _)
      calc
        _ ≤ |u * scaledSum M hM f p| := le_abs_self _
        _ = |u| * |scaledSum M hM f p| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hu (abs_nonneg _)
    have hupp := integral_mono (hi u) ((hi U).add (hi (-U))) hpoint
    simp only [Pi.add_apply] at hupp
    rw [integral_add (hi U) (hi (-U))] at hupp
    dsimp only [B]
    linarith only [hupp, hb, hn, (Real.exp_pos (2 * U * Real.sqrt (K : ℝ))).le]
  · have hkKreal : (k : ℝ) ≤ K := by exact_mod_cast (show k ≤ K by omega)
    have hpoint (p : State S k) : Real.exp (u * scaledSum M hM f p) ≤
        Real.exp (2 * U * Real.sqrt (K : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hab := mul_le_mul hu (hunit p) (abs_nonneg _) hU
      have hsqrt := Real.sqrt_le_sqrt hkKreal
      have hright := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 2 * U)
      calc
        _ ≤ |u * scaledSum M hM f p| := le_abs_self _
        _ = |u| * |scaledSum M hM f p| := abs_mul _ _
        _ ≤ U * (2 * Real.sqrt (k : ℝ)) := hab
        _ ≤ _ := by nlinarith only [hright]
    have hupp := integral_mono (hi u) (integrable_const _) hpoint
    simp only [integral_const, probReal_univ, smul_eq_mul] at hupp
    dsimp only [B]
    linarith only [hupp, hB₀]

/-- The actual independently sampled component states. -/
abbrev StateFamily {q : ℕ} (k : Fin q → ℕ) := (i : Fin q) → State S (k i)

/-- Literal finite product of the connected laws. -/
def productLaw (M : CompactBJRModel S) {q : ℕ} (k r : Fin q → ℕ)
    (g : Fin q → C(S, ℝ)) (hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i)) :
    Measure (StateFamily (S := S) k) := Measure.pi (fun i ↦ law M (g i) (k i) (r i) (hC i))

instance productLaw_isProbability (M : CompactBJRModel S) {q : ℕ}
    (k r : Fin q → ℕ) (g : Fin q → C(S, ℝ))
    (hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i)) :
    IsProbabilityMeasure (productLaw M k r g hC) := by
  unfold productLaw
  infer_instance

/-- Total centered fluctuation of the pooled empirical profile. -/
def pooledSum (M : CompactBJRModel S) (hM : M.IsRegularCritical) {q : ℕ}
    (k : Fin q → ℕ) (f : C(S, ℝ)) (p : StateFamily (S := S) k) : ℝ :=
    (∑ i, centeredSum M hM f (p i)) / Real.sqrt (∑ i, (k i : ℝ))

theorem pooledSum_measurable (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (k : Fin q → ℕ) (f : C(S, ℝ)) : Measurable (pooledSum M hM k f) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ ↦
    (((typeSum_continuous f).measurable.comp measurable_fst).sub measurable_const).comp
      (measurable_pi_apply i))

theorem pooledSum_smul (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (k : Fin q → ℕ) (f : C(S, ℝ)) (a : ℝ) (p : StateFamily (S := S) k) :
    pooledSum M hM k (a • f) p = a * pooledSum M hM k f p := by
  simp only [pooledSum, centeredSum_smul, ← Finset.mul_sum]
  ring

theorem pooledSum_neg (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (k : Fin q → ℕ) (f : C(S, ℝ)) (p : StateFamily (S := S) k) :
    pooledSum M hM k (-f) p = -pooledSum M hM k f p := by
  simp only [pooledSum, centeredSum_neg, Finset.sum_neg_distrib, neg_div]

theorem totalSize_pos {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    (0 : ℝ) < ∑ i, (k i : ℝ) := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  apply Finset.sum_pos (fun i _ ↦ by exact_mod_cast hk i)
  exact Finset.univ_nonempty

theorem pooledSum_abs_le (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (f : C(S, ℝ)) (p : StateFamily (S := S) k) :
    |pooledSum M hM k f p| ≤ 2 * Real.sqrt (∑ i, (k i : ℝ)) * ‖f‖ := by
  have hpos := totalSize_pos hq k hk
  have hsqpos : 0 < Real.sqrt (∑ i, (k i : ℝ)) := Real.sqrt_pos.mpr hpos
  have hsqrtSq := Real.sq_sqrt hpos.le
  rw [pooledSum, abs_div, abs_of_pos hsqpos]
  apply (div_le_iff₀ hsqpos).mpr
  calc
    _ ≤ ∑ i, |centeredSum M hM f (p i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * (k i : ℝ) * ‖f‖ := Finset.sum_le_sum (fun i _ ↦ centeredSum_abs_le M hM f (p i))
    _ = (2 * Real.sqrt (∑ i, (k i : ℝ)) * ‖f‖) * Real.sqrt (∑ i, (k i : ℝ)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      calc
        _ = 2 * Real.sqrt (∑ i, (k i : ℝ)) ^ 2 * ‖f‖ := by rw [hsqrtSq]
        _ = _ := by ring

/-- The Laplace transform factors under the actual finite product law. -/
theorem integral_exp_pooledSum_eq_prod (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (k r : Fin q → ℕ) (g : Fin q → C(S, ℝ)) (f : C(S, ℝ)) (U : ℝ)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i)) :
    (∫ p, Real.exp (U * pooledSum M hM k f p) ∂productLaw M k r g hC) =
      ∏ i, ∫ p, Real.exp ((U / Real.sqrt (∑ i, (k i : ℝ))) * centeredSum M hM f p)
        ∂law M (g i) (k i) (r i) (hC i) := by
  have hfun (p : StateFamily (S := S) k) : Real.exp (U * pooledSum M hM k f p) =
      ∏ i, Real.exp ((U / Real.sqrt (∑ i, (k i : ℝ))) * centeredSum M hM f (p i)) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [pooledSum, ← Finset.mul_sum]
    ring
  simp_rw [hfun]
  unfold productLaw
  exact integral_fintype_prod_eq_prod
    (μ := fun i ↦ law M (g i) (k i) (r i) (hC i))
    (fun i p ↦ Real.exp ((U / Real.sqrt (∑ j, (k j : ℝ))) * centeredSum M hM f p))

/-- Every fixed pooled linear tilt is uniformly bounded, including
collections with some bounded component sizes. -/
theorem exists_uniform_pooled_laplace_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R q : ℕ) (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    ∃ B : ℝ, 0 < B ∧ ∀ k r : Fin q → ℕ, (∀ i, 0 < k i) → (∀ i, r i ≤ R) →
      ∀ g : Fin q → C(S, ℝ), (∀ i, Real.sqrt (k i : ℝ) * ‖g i‖ ≤ L) →
      ∀ f : C(S, ℝ), ‖f‖ ≤ 1 →
      ∀ hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i),
      (∫ p, Real.exp (U * pooledSum M hM k f p) ∂productLaw M k r g hC) ≤ B := by
  obtain ⟨B₀, hB₀, hsingle⟩ := exists_all_size_scaled_laplace_bound M hM R L U hL hU
  refine ⟨B₀ ^ q, pow_pos hB₀ _, ?_⟩
  intro k r hk hr g hg f hf hC
  rw [integral_exp_pooledSum_eq_prod]
  have hfactor (i : Fin q) :
      (∫ p, Real.exp ((U / Real.sqrt (∑ j, (k j : ℝ))) * centeredSum M hM f p)
        ∂law M (g i) (k i) (r i) (hC i)) ≤ B₀ := by
    have hkreal : (0 : ℝ) < k i := by exact_mod_cast hk i
    have hki : (k i : ℝ) ≤ ∑ j, (k j : ℝ) :=
      Finset.single_le_sum (fun j _ ↦ Nat.cast_nonneg (k j)) (Finset.mem_univ i)
    have htotal : (0 : ℝ) < ∑ j, (k j : ℝ) := hkreal.trans_le hki
    have hsqrt := Real.sqrt_pos.mpr htotal
    have hsqki := Real.sqrt_pos.mpr hkreal
    have htilt : |U * Real.sqrt (k i : ℝ) / Real.sqrt (∑ j, (k j : ℝ))| ≤ U := by
      rw [abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ hsqrt).mpr
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hki) hU
    have hb := hsingle (k i) (hk i) (r i) (hr i) (g i) f (hg i) hf
      (U * Real.sqrt (k i : ℝ) / Real.sqrt (∑ j, (k j : ℝ))) htilt (hC i)
    have hfun (p : State S (k i)) :
        (U * Real.sqrt (k i : ℝ) / Real.sqrt (∑ j, (k j : ℝ))) * scaledSum M hM f p =
        (U / Real.sqrt (∑ j, (k j : ℝ))) * centeredSum M hM f p := by
      simp only [scaledSum]
      field_simp [hsqki.ne']
    simp_rw [hfun] at hb
    exact hb
  calc
    _ ≤ ∏ _i : Fin q, B₀ := Finset.prod_le_prod
      (fun i _ ↦ integral_nonneg (fun _ ↦ (Real.exp_pos _).le)) (fun i _ ↦ hfactor i)
    _ = _ := by simp

/-- Actual one-feature exponential-square estimate for a fixed number
of independently sampled components. -/
theorem exists_uniform_pooled_square_moment_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R q : ℕ) (hq : 0 < q) (L A : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ k r : Fin q → ℕ, (∀ i, 0 < k i) → (∀ i, r i ≤ R) →
      ∀ g : Fin q → C(S, ℝ), (∀ i, Real.sqrt (k i : ℝ) * ‖g i‖ ≤ L) →
      ∀ f : C(S, ℝ), ‖f‖ ≤ 1 → ∀ a : ℝ, 0 ≤ a → a ≤ A →
      ∀ hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i),
      0 ≤ (∫ p, Real.exp ((a / Real.sqrt (∑ i, (k i : ℝ))) * (pooledSum M hM k f p) ^ 2)
          ∂productLaw M k r g hC) - 1 ∧
        (∫ p, Real.exp ((a / Real.sqrt (∑ i, (k i : ℝ))) * (pooledSum M hM k f p) ^ 2)
          ∂productLaw M k r g hC) - 1 ≤ D / Real.sqrt (∑ i, (k i : ℝ)) := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_pooled_laplace_bound M hM R q L (2 * A + 1)
    hL (by linarith)
  let D : ℝ := 4 * A * B + 1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro k r hk hr g hg f hf a ha haA hC
  have hsqrt : 0 < Real.sqrt (∑ i, (k i : ℝ)) := Real.sqrt_pos.mpr (totalSize_pos hq k hk)
  have hfull (p : StateFamily (S := S) k) : |pooledSum M hM k f p| ≤
      2 * Real.sqrt (∑ i, (k i : ℝ)) := by
    exact (pooledSum_abs_le M hM hq k hk f p).trans
      (by
        have hm := mul_le_mul_of_nonneg_left hf
          (by positivity : 0 ≤ 2 * Real.sqrt (∑ i, (k i : ℝ)))
        simpa only [mul_one] using hm)
  have hp := hbound k r hk hr g hg f hf hC
  have hn := hbound k r hk hr g hg (-f) (by simpa only [norm_neg] using hf) hC
  simp_rw [pooledSum_neg, mul_neg, ← neg_mul] at hn
  have he := integral_exp_square_sub_one_le (productLaw M k r g hC) (pooledSum_measurable M hM k f)
    ha haA hsqrt hfull hp hn
  refine ⟨he.1, he.2.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_right haA hB.le
  have hcoef : 4 * a * B ≤ D := by dsimp only [D]; nlinarith only [hm]
  have hd := div_le_div_of_nonneg_right hcoef hsqrt.le
  convert hd using 1
  ring

theorem pooledSum_eq_norm_mul_unit (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (k : Fin q → ℕ) (f : C(S, ℝ)) (p : StateFamily (S := S) k) :
    pooledSum M hM k f p = ‖f‖ * pooledSum M hM k (unitField f) p := by
  conv_lhs => rw [field_eq_norm_smul_unitField f]
  exact pooledSum_smul M hM k (unitField f) ‖f‖ p

/-- The genuine countable feature bound under a fixed finite product of
connected laws. The common constant is independent of every component
size, of the fields, and of the particular summable feature family. -/
theorem exists_uniform_pooled_feature_square_series_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R q : ℕ) (hq : 0 < q) (L A B : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ k r : Fin q → ℕ, (∀ i, 0 < k i) → (∀ i, r i ≤ R) →
      ∀ g : Fin q → C(S, ℝ), (∀ i, Real.sqrt (k i : ℝ) * ‖g i‖ ≤ L) →
      ∀ (b : ℕ → ℝ) (f : ℕ → C(S, ℝ)), (∀ j, 0 ≤ b j) →
        Summable (fun j ↦ b j * ‖f j‖ ^ 2) → (∑' j, b j * ‖f j‖ ^ 2) ≤ B →
      ∀ hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i),
      0 ≤ (∫ p, Real.exp ((A / Real.sqrt (∑ i, (k i : ℝ))) *
            ∑' j, b j * (pooledSum M hM k (f j) p) ^ 2) ∂productLaw M k r g hC) - 1 ∧
        (∫ p, Real.exp ((A / Real.sqrt (∑ i, (k i : ℝ))) *
            ∑' j, b j * (pooledSum M hM k (f j) p) ^ 2) ∂productLaw M k r g hC) - 1 ≤
          D / Real.sqrt (∑ i, (k i : ℝ)) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_pooled_square_moment_bound M hM R q hq L
    (A * (B + 1)) hL (by positivity)
  refine ⟨D, hD, ?_⟩
  intro k r hk hr g hg b f hb hs hbudget hC
  have hsqrt : 0 < Real.sqrt (∑ i, (k i : ℝ)) := Real.sqrt_pos.mpr (totalSize_pos hq k hk)
  let c : ℕ → ℝ := fun j ↦ b j * ‖f j‖ ^ 2
  let X : ℕ → StateFamily (S := S) k → ℝ := fun j p ↦ pooledSum M hM k (unitField (f j)) p
  have hXbound (j : ℕ) (p : StateFamily (S := S) k) : |X j p| ≤ 2 * Real.sqrt (∑ i, (k i : ℝ)) := by
    exact (pooledSum_abs_le M hM hq k hk (unitField (f j)) p).trans
      (by
        have hm := mul_le_mul_of_nonneg_left (norm_unitField_le (f j))
          (by positivity : 0 ≤ 2 * Real.sqrt (∑ i, (k i : ℝ)))
        simpa only [mul_one] using hm)
  have hm (j : ℕ) : (∫ p, Real.exp ((A * (B + 1) / Real.sqrt (∑ i, (k i : ℝ))) * (X j p) ^ 2)
      ∂productLaw M k r g hC) - 1 ≤ D / Real.sqrt (∑ i, (k i : ℝ)) :=
    (hbound k r hk hr g hg (unitField (f j)) (norm_unitField_le _) (A * (B + 1))
      (by positivity) le_rfl hC).2
  have he := integral_exp_tsum_squares_sub_one_le (productLaw M k r g hC) c X
    hA (by positivity : 0 < B + 1) hsqrt
    (by positivity : 0 ≤ D / Real.sqrt (∑ i, (k i : ℝ)))
    (fun j ↦ mul_nonneg (hb j) (sq_nonneg _)) hs (by dsimp only [c]; linarith)
    (fun j ↦ pooledSum_measurable M hM k (unitField (f j))) hXbound hm
  have hterms (j : ℕ) (p : StateFamily (S := S) k) :
      c j * (X j p) ^ 2 = b j * (pooledSum M hM k (f j) p) ^ 2 := by
    rw [pooledSum_eq_norm_mul_unit M hM k (f j) p]
    dsimp only [c, X]
    ring
  simp_rw [hterms] at he
  exact he

end PerronWright.ProfileFiniteCollection
