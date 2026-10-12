import PerronWright.Probability.ProfileSquareMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite and countable summable feature-square exponential bounds

Finite feature sums use convexity with unused budget placed at zero.
Countable sums are reached by actual dominated convergence of their
finite partial sums; no square-moment or UI interface is postulated.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology Real

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.ProfileSquareSeries

open ProfileSquareMoment ProfileLaplace ConnectedTypeLaw

section Jensen

variable {ι : Type*}

/-- Finite weighted Jensen domination with an unused positive budget. -/
theorem exp_weighted_squares_sub_one_le (t : Finset ι) (c Y : ι → ℝ)
    {A B q : ℝ} (hB : 0 < B) (hc : ∀ i ∈ t, 0 ≤ c i)
    (hbudget : ∑ i ∈ t, c i ≤ B) :
    Real.exp ((A / q) * ∑ i ∈ t, c i * (Y i) ^ 2) - 1 ≤
      ∑ i ∈ t, (c i / B) * (Real.exp ((A * B / q) * (Y i) ^ 2) - 1) := by
  let w : ι → ℝ := fun i ↦ c i / B
  have hw : ∀ i ∈ t, 0 ≤ w i := fun i hi ↦ div_nonneg (hc i hi) hB.le
  have hsumw : ∑ i ∈ t, w i ≤ 1 := by
    simp only [w, ← Finset.sum_div]
    exact (div_le_one hB).mpr hbudget
  have hj := convexOn_exp.map_add_sum_le (t := t) (w := w)
    (p := fun i ↦ (A * B / q) * (Y i) ^ 2) (v := 1 - ∑ i ∈ t, w i)
    (q := (0 : ℝ)) hw (by ring) (fun _ _ ↦ Set.mem_univ _)
    (by linarith) (Set.mem_univ _)
  have hin : ∑ i ∈ t, w i * ((A * B / q) * (Y i) ^ 2) =
      (A / q) * ∑ i ∈ t, c i * (Y i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [w]
    field_simp [hB.ne']
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, hin] at hj
  have hout : (1 - ∑ i ∈ t, w i) +
      (∑ i ∈ t, w i * Real.exp ((A * B / q) * (Y i) ^ 2)) - 1 =
      ∑ i ∈ t, w i * (Real.exp ((A * B / q) * (Y i) ^ 2) - 1) := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
    ring
  rw [← hout]
  linarith only [hj]

end Jensen

section ProbabilityJensen

variable {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integral_exp_finset_squares_sub_one_le (t : Finset ι)
    (c : ι → ℝ) (X : ι → Ω → ℝ) {A B q err : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hq : 0 < q) (herr : 0 ≤ err)
    (hc : ∀ i ∈ t, 0 ≤ c i) (hbudget : ∑ i ∈ t, c i ≤ B)
    (hX : ∀ i ∈ t, Measurable (X i))
    (hXbound : ∀ i ∈ t, ∀ x, |X i x| ≤ 2 * q)
    (hmoment : ∀ i ∈ t,
      (∫ x, Real.exp ((A * B / q) * (X i x) ^ 2) ∂μ) - 1 ≤ err) :
    0 ≤ (∫ x, Real.exp ((A / q) * ∑ i ∈ t, c i * (X i x) ^ 2) ∂μ) - 1 ∧
      (∫ x, Real.exp ((A / q) * ∑ i ∈ t, c i * (X i x) ^ 2) ∂μ) - 1 ≤ err := by
  have hsumMeas : Measurable (fun x ↦ ∑ i ∈ t, c i * (X i x) ^ 2) :=
    Finset.measurable_fun_sum t (fun i hi ↦ ((hX i hi).pow_const 2).const_mul _)
  have hsumBound (x : Ω) : ∑ i ∈ t, c i * (X i x) ^ 2 ≤ B * (2 * q) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ t, c i * (2 * q) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (hc i hi)
        simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg (X i x)) (hXbound i hi x) 2
      _ = (∑ i ∈ t, c i) * (2 * q) ^ 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (sq_nonneg _)
  have hi : Integrable (fun x ↦ Real.exp ((A / q) * ∑ i ∈ t, c i * (X i x) ^ 2)) μ := by
    apply integrable_of_measurable_abs_le μ (hsumMeas.const_mul _).exp
    intro x
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hsumBound x) (by positivity))
  have hione (i : ι) (hi : i ∈ t) :
      Integrable (fun x ↦ Real.exp ((A * B / q) * (X i x) ^ 2)) μ := by
    apply integrable_of_measurable_abs_le μ (((hX i hi).pow_const 2).const_mul _).exp
    intro x
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (X i x)) (hXbound i hi x) 2)
      (by positivity))
  have hiSub := hi.sub (integrable_const (1 : ℝ))
  have hiMajor : Integrable (fun x ↦ ∑ i ∈ t,
      (c i / B) * (Real.exp ((A * B / q) * (X i x) ^ 2) - 1)) μ := by
    apply integrable_finsetSum
    intro i hi
    exact ((hione i hi).sub (integrable_const _)).const_mul _
  have hj := integral_mono hiSub hiMajor (fun x ↦
    exp_weighted_squares_sub_one_le t c (fun i ↦ X i x) hB hc hbudget)
  simp only [Pi.sub_apply] at hj
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ,
    smul_eq_mul, mul_one, integral_finsetSum] at hj
  · simp_rw [integral_const_mul] at hj
    have hj' : (∫ x, Real.exp ((A / q) * ∑ i ∈ t, c i * (X i x) ^ 2) ∂μ) - 1 ≤
        ∑ i ∈ t, (c i / B) * err := by
      refine hj.trans (Finset.sum_le_sum ?_)
      intro i hi
      rw [integral_sub (hione i hi) (integrable_const _), integral_const,
        probReal_univ, smul_eq_mul, mul_one]
      exact mul_le_mul_of_nonneg_left (hmoment i hi) (div_nonneg (hc i hi) hB.le)
    have hbudget' : ∑ i ∈ t, c i / B ≤ 1 := by
      rw [← Finset.sum_div]
      exact (div_le_one hB).mpr hbudget
    have hlast : (∑ i ∈ t, (c i / B) * err) ≤ err := by
      rw [← Finset.sum_mul]
      exact (mul_le_mul_of_nonneg_right hbudget' herr).trans_eq (by ring)
    have hl := integral_mono (integrable_const (1 : ℝ)) hi (fun x ↦
      Real.one_le_exp_iff.mpr (mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun i hi ↦ mul_nonneg (hc i hi) (sq_nonneg _)))))
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hl
    exact ⟨by linarith, hj'.trans hlast⟩
  · intro i hi
    exact ((hione i hi).sub (integrable_const _)).const_mul _

end ProbabilityJensen

section CountableProbabilityJensen

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The countable weighted bound follows by dominated convergence of
literal finite partial sums with the same deterministic majorant. -/
theorem integral_exp_tsum_squares_sub_one_le (c : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    {A B q err : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hq : 0 < q) (herr : 0 ≤ err)
    (hc : ∀ i, 0 ≤ c i) (hcs : Summable c) (hbudget : ∑' i, c i ≤ B)
    (hX : ∀ i, Measurable (X i)) (hXbound : ∀ i x, |X i x| ≤ 2 * q)
    (hmoment : ∀ i, (∫ x, Real.exp ((A * B / q) * (X i x) ^ 2) ∂μ) - 1 ≤ err) :
    0 ≤ (∫ x, Real.exp ((A / q) * ∑' i, c i * (X i x) ^ 2) ∂μ) - 1 ∧
      (∫ x, Real.exp ((A / q) * ∑' i, c i * (X i x) ^ 2) ∂μ) - 1 ≤ err := by
  have hterm (i : ℕ) (x : Ω) : c i * (X i x) ^ 2 ≤ c i * (2 * q) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (hc i)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (X i x)) (hXbound i x) 2
  have hs (x : Ω) : Summable (fun i ↦ c i * (X i x) ^ 2) :=
    (hcs.mul_right ((2 * q) ^ 2)).of_nonneg_of_le
      (fun i ↦ mul_nonneg (hc i) (sq_nonneg _)) (fun i ↦ hterm i x)
  let F : ℕ → Ω → ℝ := fun N x ↦
    Real.exp ((A / q) * ∑ i ∈ Finset.range N, c i * (X i x) ^ 2)
  let G : Ω → ℝ := fun x ↦ Real.exp ((A / q) * ∑' i, c i * (X i x) ^ 2)
  have hFmeas (N : ℕ) : Measurable (F N) :=
    ((Finset.measurable_fun_sum (Finset.range N)
      (fun i _ ↦ ((hX i).pow_const 2).const_mul _)).const_mul _).exp
  have hpartial (N : ℕ) : ∑ i ∈ Finset.range N, c i ≤ B :=
    (hcs.sum_le_tsum _ (fun i _ ↦ hc i)).trans hbudget
  have hFbound (N : ℕ) (x : Ω) : ‖F N x‖ ≤ Real.exp ((A / q) * (B * (2 * q) ^ 2)) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ ∑ i ∈ Finset.range N, c i * (2 * q) ^ 2 :=
        Finset.sum_le_sum (fun i _ ↦ hterm i x)
      _ = (∑ i ∈ Finset.range N, c i) * (2 * q) ^ 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hpartial N) (sq_nonneg _)
  have hFlim (x : Ω) : Tendsto (fun N ↦ F N x) atTop (𝓝 (G x)) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul ((hs x).hasSum.tendsto_sum_nat))
  have hInt := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ : Ω ↦ Real.exp ((A / q) * (B * (2 * q) ^ 2)))
    (fun N ↦ (hFmeas N).aestronglyMeasurable) (integrable_const _)
    (fun N ↦ Eventually.of_forall (hFbound N)) (Eventually.of_forall hFlim)
  have hIntSub := hInt.sub_const (1 : ℝ)
  have hfinite (N : ℕ) :
      0 ≤ (∫ x, F N x ∂μ) - 1 ∧ (∫ x, F N x ∂μ) - 1 ≤ err := by
    exact integral_exp_finset_squares_sub_one_le μ (Finset.range N) c X hA hB hq herr
      (fun i _ ↦ hc i) (hpartial N) (fun i _ ↦ hX i)
      (fun i _ ↦ hXbound i) (fun i _ ↦ hmoment i)
  exact ⟨ge_of_tendsto hIntSub (Eventually.of_forall (fun N ↦ (hfinite N).1)),
    le_of_tendsto hIntSub (Eventually.of_forall (fun N ↦ (hfinite N).2))⟩

end CountableProbabilityJensen

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Uniform summable-feature square moments under the actual connected
type law. The coefficient and feature families may vary with size; only
their common projective budget is constrained. -/
theorem exists_uniform_feature_square_series_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L A B : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop, 0 < k ∧
      ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ), Real.sqrt (k : ℝ) * ‖g‖ ≤ L →
        ∀ (b : ℕ → ℝ) (f : ℕ → C(S, ℝ)), (∀ j, 0 ≤ b j) →
          Summable (fun j ↦ b j * ‖f j‖ ^ 2) → (∑' j, b j * ‖f j‖ ^ 2) ≤ B →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
          0 ≤ (∫ p, Real.exp ((A / Real.sqrt (k : ℝ)) *
              ∑' j, b j * (scaledSum M hM (f j) p) ^ 2) ∂law M g k r hC) - 1 ∧
            (∫ p, Real.exp ((A / Real.sqrt (k : ℝ)) *
              ∑' j, b j * (scaledSum M hM (f j) p) ^ 2) ∂law M g k r hC) - 1 ≤
              D / Real.sqrt (k : ℝ) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_scaled_square_moment_bound M hM R L
    (A * (B + 1)) hL (by positivity)
  refine ⟨D, hD, ?_⟩
  filter_upwards [hbound] with k hk
  refine ⟨hk.1, ?_⟩
  intro r hr g hg b f hb hs hbudget hCg
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hq : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  let c : ℕ → ℝ := fun j ↦ b j * ‖f j‖ ^ 2
  let X : ℕ → State S k → ℝ := fun j p ↦ scaledSum M hM (unitField (f j)) p
  have hXbound (j : ℕ) (p : State S k) : |X j p| ≤ 2 * Real.sqrt (k : ℝ) := by
    exact (scaledSum_abs_le M hM hk.1 (unitField (f j)) p).trans
      (by
        have hm := mul_le_mul_of_nonneg_left (norm_unitField_le (f j))
          (by positivity : 0 ≤ 2 * Real.sqrt (k : ℝ))
        simpa only [mul_one] using hm)
  have hm (j : ℕ) : (∫ p, Real.exp ((A * (B + 1) / Real.sqrt (k : ℝ)) * (X j p) ^ 2)
      ∂law M g k r hCg) - 1 ≤ D / Real.sqrt (k : ℝ) :=
    (hk.2 r hr g (unitField (f j)) hg (norm_unitField_le _) (A * (B + 1))
      (by positivity) le_rfl hCg).2
  have he := integral_exp_tsum_squares_sub_one_le (law M g k r hCg) c X
    hA (by positivity : 0 < B + 1) hq (by positivity : 0 ≤ D / Real.sqrt (k : ℝ))
    (fun j ↦ mul_nonneg (hb j) (sq_nonneg _)) hs (by dsimp only [c]; linarith)
    (fun j ↦ scaledSum_measurable M hM (unitField (f j))) hXbound hm
  have hterms (j : ℕ) (p : State S k) :
      c j * (X j p) ^ 2 = b j * (scaledSum M hM (f j) p) ^ 2 := by
    rw [scaledSum_eq_norm_mul_unit M hM (f j) p]
    dsimp only [c, X]
    ring
  simp_rw [hterms] at he
  exact he

end PerronWright.ProfileSquareSeries
