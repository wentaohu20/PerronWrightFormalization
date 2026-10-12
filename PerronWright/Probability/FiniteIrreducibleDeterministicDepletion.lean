import PerronWright.Analysis.FinitePopulationLog
import PerronWright.Model.FiniteIrreducibleModel
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.Finite

/-! # Literal finite-type depletion and deterministic population correction

The population counts are arbitrary natural counts, not a rounding
algorithm. All selection factors below use actual descending factorials.
The estimates are deterministic and require no profile assumption.
-/

open Filter Topology MeasureTheory
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FiniteIrreducibleDeterministicDepletion

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Literal normalized product of within-type placement multiplicities. -/
def normalizedDepletion (c K : S → ℕ) : ℝ :=
  ∏ a, ((c a).descFactorial (K a) : ℝ) / (c a : ℝ) ^ K a

omit [DecidableEq S] in
theorem normalizedDepletion_pos (c K : S → ℕ)
    (hc : ∀ a, 0 < c a) (hK : ∀ a, K a ≤ c a) :
    0 < normalizedDepletion c K := by
  exact Finset.prod_pos (fun a _ ↦ div_pos
    (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr (hK a)))
    (pow_pos (Nat.cast_pos.mpr (hc a)) _))

omit [DecidableEq S] in
theorem log_normalizedDepletion (c K : S → ℕ)
    (hc : ∀ a, 0 < c a) (hK : ∀ a, K a ≤ c a) :
    Real.log (normalizedDepletion c K) =
      ∑ a, Real.log (((c a).descFactorial (K a) : ℝ) / (c a : ℝ) ^ K a) := by
  apply Real.log_prod
  intro a _
  exact (div_pos (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr (hK a)))
    (pow_pos (Nat.cast_pos.mpr (hc a)) _)).ne'

omit [DecidableEq S] in
/-- Exact polynomial depletion expansion with a fourth-order bound,
simultaneously for every actual type count vector. -/
theorem log_normalizedDepletion_polynomial_error (c K : S → ℕ)
    (hc : ∀ a, 0 < c a) (hhalf : ∀ a, (K a : ℝ) ≤ (c a : ℝ) / 2) :
    |Real.log (normalizedDepletion c K) +
      ∑ a, (K a : ℝ) * ((K a : ℝ) - 1) / (2 * c a) +
      ∑ a, (K a : ℝ) * ((K a : ℝ) - 1) * (2 * (K a : ℝ) - 1) /
        (12 * (c a : ℝ) ^ 2)| ≤
      ∑ a, 2 * (K a : ℝ) ^ 4 / (c a : ℝ) ^ 3 := by
  have hK : ∀ a, K a ≤ c a := fun a ↦ by
    have h := hhalf a
    have hn : (0 : ℝ) ≤ c a := Nat.cast_nonneg _
    exact_mod_cast (show (K a : ℝ) ≤ c a by linarith)
  rw [log_normalizedDepletion c K hc hK, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun a _ ↦ FinitePopulationLog.log_selection_polynomial_error
      (hc a) (hhalf a)))

theorem log_selection_leading_error {n K : ℕ} (hn : 0 < n)
    (hhalf : (K : ℝ) ≤ (n : ℝ) / 2) :
    |Real.log ((n.descFactorial K : ℝ) / (n : ℝ) ^ K) +
        (K : ℝ) ^ 2 / (2 * n) + (K : ℝ) ^ 3 / (6 * (n : ℝ) ^ 2)| ≤
      2 * (K : ℝ) ^ 4 / (n : ℝ) ^ 3 +
        (K : ℝ) / (2 * n) + (K : ℝ) ^ 2 / (4 * (n : ℝ) ^ 2) +
        (K : ℝ) / (12 * (n : ℝ) ^ 2) := by
  have hp := FinitePopulationLog.log_selection_polynomial_error hn hhalf
  have heq : Real.log ((n.descFactorial K : ℝ) / (n : ℝ) ^ K) +
      (K : ℝ) ^ 2 / (2 * n) + (K : ℝ) ^ 3 / (6 * (n : ℝ) ^ 2) =
      (Real.log ((n.descFactorial K : ℝ) / (n : ℝ) ^ K) +
        (K : ℝ) * ((K : ℝ) - 1) / (2 * n) +
        (K : ℝ) * ((K : ℝ) - 1) * (2 * (K : ℝ) - 1) / (12 * (n : ℝ) ^ 2)) +
      ((K : ℝ) / (2 * n) + (K : ℝ) ^ 2 / (4 * (n : ℝ) ^ 2) -
        (K : ℝ) / (12 * (n : ℝ) ^ 2)) := by ring
  rw [heq]
  have hnonneg : 0 ≤ (K : ℝ) / (2 * n) + (K : ℝ) ^ 2 / (4 * (n : ℝ) ^ 2) := by positivity
  have hab := abs_sub ((K : ℝ) / (2 * n) + (K : ℝ) ^ 2 / (4 * (n : ℝ) ^ 2))
    ((K : ℝ) / (12 * (n : ℝ) ^ 2))
  have hthird : 0 ≤ (K : ℝ) / (12 * (n : ℝ) ^ 2) := by positivity
  rw [abs_of_nonneg hnonneg, abs_of_nonneg hthird] at hab
  exact (abs_add_le _ _).trans (by linarith)

omit [DecidableEq S] in
/-- The paper's leading quadratic/cubic depletion exponent, with an
explicit error valid uniformly over all type count vectors. -/
theorem log_normalizedDepletion_leading_error (c K : S → ℕ)
    (hc : ∀ a, 0 < c a) (hhalf : ∀ a, (K a : ℝ) ≤ (c a : ℝ) / 2) :
    |Real.log (normalizedDepletion c K) +
      ∑ a, (K a : ℝ) ^ 2 / (2 * c a) +
      ∑ a, (K a : ℝ) ^ 3 / (6 * (c a : ℝ) ^ 2)| ≤
      ∑ a, (2 * (K a : ℝ) ^ 4 / (c a : ℝ) ^ 3 +
        (K a : ℝ) / (2 * c a) + (K a : ℝ) ^ 2 / (4 * (c a : ℝ) ^ 2) +
        (K a : ℝ) / (12 * (c a : ℝ) ^ 2)) := by
  have hK : ∀ a, K a ≤ c a := fun a ↦ by
    have h := hhalf a
    have hn : (0 : ℝ) ≤ c a := Nat.cast_nonneg _
    exact_mod_cast (show (K a : ℝ) ≤ c a by linarith)
  rw [log_normalizedDepletion c K hc hK, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun a _ ↦ log_selection_leading_error (hc a) (hhalf a)))

/-- Actual empirical ambient frequency, with zero-size convention. -/
def empiricalFrequency (n : ℕ) (c : S → ℕ) (a : S) : ℝ := (c a : ℝ) / n

theorem empiricalFrequency_error (M : FiniteIrreducibleModel S)
    {n : ℕ} (hn : 0 < n) (c : S → ℕ) {D : ℝ}
    (hround : ∀ a, |(c a : ℝ) - (n : ℝ) * M.weight a| ≤ D) (a : S) :
    |empiricalFrequency n c a - M.weight a| ≤ D / n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : empiricalFrequency n c a - M.weight a =
      ((c a : ℝ) - (n : ℝ) * M.weight a) / n := by
    unfold empiricalFrequency
    field_simp
  rw [heq, abs_div, abs_of_pos hnR]
  exact div_le_div_of_nonneg_right (hround a) hnR.le

/-- O(1) rounding yields actual ν→μ, with no chosen rounding scheme. -/
theorem empiricalFrequency_tendsto (M : FiniteIrreducibleModel S)
    (c : ℕ → S → ℕ) (D : ℝ)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (a : S) : Tendsto (fun n ↦ empiricalFrequency n (c n) a) atTop (𝓝 (M.weight a)) := by
  have hupper : Tendsto (fun n : ℕ ↦ D / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul D
  have herr : Tendsto (fun n ↦ |empiricalFrequency n (c n) a - M.weight a|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hupper
    filter_upwards [hround, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    exact empiricalFrequency_error M (by omega) (c n) hn a
  simpa only [Real.norm_eq_abs] using (tendsto_iff_norm_sub_tendsto_zero.mpr herr)

/-- Literal mismatch of degrees under ν and the target μ. -/
def degreeCorrection (M : FiniteIrreducibleModel S) (n : ℕ) (c : S → ℕ) (a : S) : ℝ :=
  ∑ b, M.kernel a b * (empiricalFrequency n c b - M.weight b)

theorem degreeCorrection_error (M : FiniteIrreducibleModel S)
    {n : ℕ} (hn : 0 < n) (c : S → ℕ) {D : ℝ}
    (hround : ∀ a, |(c a : ℝ) - (n : ℝ) * M.weight a| ≤ D) (a : S) :
    |degreeCorrection M n c a| ≤ (∑ b, |M.kernel a b|) * (D / n) := by
  unfold degreeCorrection
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (empiricalFrequency_error M hn c hround b) (abs_nonneg _)

/-- The population correction when component laws use the fixed μ model. -/
def populationCorrection (M : FiniteIrreducibleModel S) (n : ℕ)
    (c K : S → ℕ) (t : ℝ) : ℝ :=
  (∏ a, ((c a : ℝ) / ((n : ℝ) * M.weight a)) ^ K a) *
    Real.exp (-t * ∑ a, (K a : ℝ) * degreeCorrection M n c a)

theorem populationCorrection_pos (M : FiniteIrreducibleModel S) {n : ℕ}
    (hn : 0 < n) (c K : S → ℕ) (hc : ∀ a, 0 < c a) (t : ℝ) :
    0 < populationCorrection M n c K t := by
  apply mul_pos (Finset.prod_pos (fun a _ ↦ pow_pos
    (div_pos (Nat.cast_pos.mpr (hc a)) (mul_pos (Nat.cast_pos.mpr hn) (M.weight_pos a))) _))
  exact Real.exp_pos _

theorem log_populationCorrection (M : FiniteIrreducibleModel S) {n : ℕ}
    (hn : 0 < n) (c K : S → ℕ) (hc : ∀ a, 0 < c a) (t : ℝ) :
    Real.log (populationCorrection M n c K t) =
      ∑ a, (K a : ℝ) *
        (Real.log ((c a : ℝ) / ((n : ℝ) * M.weight a)) - t * degreeCorrection M n c a) := by
  unfold populationCorrection
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr (fun a _ ↦
      pow_ne_zero _ (div_pos (Nat.cast_pos.mpr (hc a))
        (mul_pos (Nat.cast_pos.mpr hn) (M.weight_pos a))).ne')) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_prod (fun a _ ↦ pow_ne_zero _
      (div_pos (Nat.cast_pos.mpr (hc a))
        (mul_pos (Nat.cast_pos.mpr hn) (M.weight_pos a))).ne')]
  simp only [Real.log_pow, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem abs_log_one_add_le_two_abs {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x)| ≤ 2 * |x| := by
  have hs : |-x| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hs 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, abs_neg, zero_add,
    pow_one, sub_neg_eq_add] at h
  have hd : 0 < 1 - |x| := by linarith
  exact h.trans ((div_le_iff₀ hd).mpr (by nlinarith [abs_nonneg x]))

theorem log_count_ratio_error (M : FiniteIrreducibleModel S) {n : ℕ}
    (hn : 0 < n) (c : S → ℕ) {D : ℝ}
    (hround : ∀ a, |(c a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (a : S) (hsmall : D / ((n : ℝ) * M.weight a) ≤ 1 / 2) :
    |Real.log ((c a : ℝ) / ((n : ℝ) * M.weight a))| ≤
      2 * D / ((n : ℝ) * M.weight a) := by
  have hd : 0 < (n : ℝ) * M.weight a := mul_pos (Nat.cast_pos.mpr hn) (M.weight_pos a)
  have hx : |((c a : ℝ) - (n : ℝ) * M.weight a) / ((n : ℝ) * M.weight a)| ≤
      D / ((n : ℝ) * M.weight a) := by
    rw [abs_div, abs_of_pos hd]
    exact div_le_div_of_nonneg_right (hround a) hd.le
  have heq : (c a : ℝ) / ((n : ℝ) * M.weight a) =
      1 + ((c a : ℝ) - (n : ℝ) * M.weight a) / ((n : ℝ) * M.weight a) := by
    field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne', (M.weight_pos a).ne']
    ring
  rw [heq]
  exact (abs_log_one_add_le_two_abs (hx.trans hsmall)).trans
    (by convert mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2) using 1; ring)

def populationBudget (M : FiniteIrreducibleModel S) (D T : ℝ) : ℝ :=
  ∑ a, (2 * D / M.weight a + T * D * ∑ b, |M.kernel a b|)

theorem populationBudget_nonneg (M : FiniteIrreducibleModel S)
    {D T : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T) : 0 ≤ populationBudget M D T := by
  apply Finset.sum_nonneg
  intro a _
  have hμ := M.weight_pos a
  positivity

/-- Actual log population correction is uniformly O(total selected size/n),
including the literal ν−μ degree error. -/
theorem log_populationCorrection_abs_le (M : FiniteIrreducibleModel S) {n : ℕ}
    (hn : 0 < n) (c K : S → ℕ) (hc : ∀ a, 0 < c a)
    {D T t : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T) (ht : |t| ≤ T)
    (hround : ∀ a, |(c a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (hsmall : ∀ a, D / ((n : ℝ) * M.weight a) ≤ 1 / 2) :
    |Real.log (populationCorrection M n c K t)| ≤
      populationBudget M D T * (∑ a, (K a : ℝ)) / n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let A : S → ℝ := fun a ↦ 2 * D / M.weight a + T * D * ∑ b, |M.kernel a b|
  have hA : ∀ a, 0 ≤ A a := fun a ↦ by
    have hμ := M.weight_pos a
    dsimp only [A]
    positivity
  have hAB : ∀ a, A a ≤ populationBudget M D T := fun a ↦
    Finset.single_le_sum (fun b _ ↦ hA b) (Finset.mem_univ a)
  have hfield (a : S) :
      |Real.log ((c a : ℝ) / ((n : ℝ) * M.weight a)) - t * degreeCorrection M n c a| ≤ A a / n := by
    have hl := log_count_ratio_error M hn c hround a (hsmall a)
    have hg := degreeCorrection_error M hn c hround a
    have hd : |t * degreeCorrection M n c a| ≤ T * ((∑ b, |M.kernel a b|) * (D / n)) := by
      rw [abs_mul]
      exact mul_le_mul ht hg (abs_nonneg _) hT
    refine (abs_sub _ _).trans ((add_le_add hl hd).trans_eq ?_)
    dsimp only [A]
    ring
  rw [log_populationCorrection M hn c K hc t]
  calc
    _ ≤ ∑ a, |(K a : ℝ) *
        (Real.log ((c a : ℝ) / ((n : ℝ) * M.weight a)) - t * degreeCorrection M n c a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, (K a : ℝ) * (A a / n) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hfield a) (Nat.cast_nonneg _)
    _ ≤ ∑ a, (K a : ℝ) * (populationBudget M D T / n) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hAB a) hnR.le) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Counts with O(1) error are eventually positive for every type and
lie in the actual logarithmic-ratio domain, uniformly over the type set. -/
theorem eventually_count_ratio_domain (M : FiniteIrreducibleModel S)
    (c : ℕ → S → ℕ) (D : ℝ)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ (∀ a, 0 < c n a) ∧
      (∀ a, D / ((n : ℝ) * M.weight a) ≤ 1 / 2) := by
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ a : S, D / ((n : ℝ) * M.weight a) ≤ 1 / 2 := by
    apply eventually_all.mpr
    intro a
    have ht : Tendsto (fun n : ℕ ↦ D / ((n : ℝ) * M.weight a)) atTop (𝓝 0) := by
      have hh := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (D / M.weight a)
      simpa only [Function.comp_apply, mul_zero, zero_mul, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm,
        mul_left_comm] using hh
    exact (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      (fun _ h ↦ h.le)
  filter_upwards [hround, hsmall, eventually_ge_atTop (1 : ℕ)] with n hr hs hn1
  have hn : 0 < n := by omega
  refine ⟨hn, ?_, hs⟩
  intro a
  have hd : 0 < (n : ℝ) * M.weight a := mul_pos (Nat.cast_pos.mpr hn) (M.weight_pos a)
  have hD := (div_le_iff₀ hd).mp (hs a)
  have hlow := (abs_le.mp (hr a)).1
  have hp : (0 : ℝ) < c n a := by linarith
  exact_mod_cast hp

/-- Uniform literal population correction on the n^(2/3) size window.
No random profile restriction is imposed; every integer vector is covered. -/
theorem populationCorrection_uniform_log_bound (M : FiniteIrreducibleModel S)
    (c : ℕ → S → ℕ) (D T C : ℝ) (hD : 0 ≤ D) (hT : 0 ≤ T) (_hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) :
    ∀ᶠ n : ℕ in atTop, ∀ K : S → ℕ, ∀ t : ℝ,
      (∑ a, (K a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) → |t| ≤ T →
      0 < populationCorrection M n (c n) K t ∧
      |Real.log (populationCorrection M n (c n) K t)| ≤
        populationBudget M D T * C * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  filter_upwards [hround, eventually_count_ratio_domain M c D hround] with n hr hd
  intro K t hsize ht
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hd.1
  refine ⟨populationCorrection_pos M hd.1 (c n) K hd.2.1 t, ?_⟩
  have hB := populationBudget_nonneg M hD hT
  have hb := log_populationCorrection_abs_le M hd.1 (c n) K hd.2.1 hD hT ht hr hd.2.2
  refine hb.trans ?_
  have he : (n : ℝ) ^ (2 / 3 : ℝ) / n = (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have hh := Real.rpow_sub hnR (2 / 3 : ℝ) 1
    norm_num only [Real.rpow_one] at hh
    convert hh.symm using 1
  calc
    _ ≤ populationBudget M D T * (C * (n : ℝ) ^ (2 / 3 : ℝ)) / n := by
      gcongr
    _ = populationBudget M D T * C * ((n : ℝ) ^ (2 / 3 : ℝ) / n) := by ring
    _ = _ := by rw [he]

/-- The actual fixed-μ population correction tends to one for arbitrary
critical-size integer profiles. This includes the real ν−μ correction. -/
theorem populationCorrection_tendsto_one (M : FiniteIrreducibleModel S)
    (c K : ℕ → S → ℕ) (t : ℕ → ℝ) (D T C : ℝ)
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (hsize : ∀ᶠ n in atTop, (∑ a, (K n a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ))
    (ht : ∀ᶠ n in atTop, |t n| ≤ T) :
    Tendsto (fun n ↦ populationCorrection M n (c n) (K n) (t n)) atTop (𝓝 1) := by
  have hbound := populationCorrection_uniform_log_bound M c D T C hD hT hC hround
  have hzero : Tendsto (fun n : ℕ ↦ populationBudget M D T * C *
      (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop).const_mul (populationBudget M D T * C)
  have hlog : Tendsto (fun n ↦ Real.log (populationCorrection M n (c n) (K n) (t n)))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) _ hzero
    filter_upwards [hbound, hsize, ht] with n hb hs htn
    simpa only [Real.norm_eq_abs] using (hb (K n) (t n) hs htn).2
  have he := Real.continuous_exp.tendsto (0 : ℝ) |>.comp hlog
  simp only [Real.exp_zero] at he
  apply he.congr'
  filter_upwards [hbound, hsize, ht] with n hb hs htn
  exact Real.exp_log (hb (K n) (t n) hs htn).1

theorem typeCount_tendsto_atTop (M : FiniteIrreducibleModel S)
    (c : ℕ → S → ℕ) (D : ℝ)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (a : S) : Tendsto (fun n ↦ c n a) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have ht := tendsto_natCast_atTop_atTop.atTop_mul_pos (M.weight_pos a)
    (empiricalFrequency_tendsto M c D hround a)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  dsimp only [empiricalFrequency]
  field_simp

def typeScale (M : FiniteIrreducibleModel S) (C : ℝ) (a : S) : ℝ :=
  C * (2 / M.weight a) ^ (2 / 3 : ℝ)

theorem typeScale_nonneg (M : FiniteIrreducibleModel S) {C : ℝ} (hC : 0 ≤ C) (a : S) :
    0 ≤ typeScale M C a := by
  unfold typeScale
  have hμ := M.weight_pos a
  positivity

theorem type_critical_size_bound (M : FiniteIrreducibleModel S) {n : ℕ}
    (c K : S → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hlow : ∀ a, (n : ℝ) * M.weight a / 2 ≤ c a)
    (hsize : (∑ a, (K a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) (a : S) :
    (K a : ℝ) ≤ typeScale M C a * (c a : ℝ) ^ (2 / 3 : ℝ) := by
  have hnn : (n : ℝ) ≤ (2 / M.weight a) * (c a : ℝ) := by
    have h := hlow a
    have hμ := M.weight_pos a
    calc
      (n : ℝ) ≤ (2 * (c a : ℝ)) / M.weight a := (le_div_iff₀ hμ).mpr (by linarith)
      _ = _ := by ring
  have hr := Real.rpow_le_rpow (Nat.cast_nonneg n) hnn (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [Real.mul_rpow (by have hμ := M.weight_pos a; positivity) (Nat.cast_nonneg _)] at hr
  have hsum : (K a : ℝ) ≤ ∑ b, (K b : ℝ) :=
    Finset.single_le_sum (fun b _ ↦ Nat.cast_nonneg _) (Finset.mem_univ a)
  exact hsum.trans (hsize.trans (by dsimp only [typeScale]; nlinarith))

theorem critical_ratio_bound {n K : ℕ} (hn : 0 < n) {C : ℝ}
    (hsize : (K : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    (K : ℝ) / n ≤ C * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he : (n : ℝ) ^ (2 / 3 : ℝ) / n = (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have hh := Real.rpow_sub hnR (2 / 3 : ℝ) 1
    norm_num only [Real.rpow_one] at hh
    convert hh.symm using 1
  exact (div_le_div_of_nonneg_right hsize hnR.le).trans_eq (by rw [mul_div_assoc, he])

/-- A literal, vanishing envelope for the simplified log depletion error. -/
def leadingErrorEnvelope (n : ℕ) (C : ℝ) : ℝ :=
  2 * C ^ 4 * (n : ℝ) ^ (-(1 / 3 : ℝ)) +
    (C / 2) * (n : ℝ) ^ (-(1 / 3 : ℝ)) +
    (C ^ 2 / 4) * (n : ℝ) ^ (-(2 / 3 : ℝ)) +
    (C / 12) * (n : ℝ) ^ (-(4 / 3 : ℝ))

theorem leadingErrorEnvelope_tendsto_zero (N : ℕ → ℕ)
    (hNt : Tendsto N atTop atTop) (C : ℝ) :
    Tendsto (fun n ↦ leadingErrorEnvelope (N n) C) atTop (𝓝 0) := by
  have ht (x : ℝ) (hx : 0 < x) :
      Tendsto (fun n ↦ (N n : ℝ) ^ (-x)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hx).comp (tendsto_natCast_atTop_atTop.comp hNt)
  simpa only [mul_zero, zero_add, leadingErrorEnvelope] using
    (((ht (1 / 3) (by norm_num)).const_mul (2 * C ^ 4)).add
      ((ht (1 / 3) (by norm_num)).const_mul (C / 2)) |>.add
        ((ht (2 / 3) (by norm_num)).const_mul (C ^ 2 / 4)) |>.add
          ((ht (4 / 3) (by norm_num)).const_mul (C / 12)))

theorem log_selection_leading_error_envelope {n K : ℕ} (hn : 0 < n)
    {C : ℝ} (hC : 0 ≤ C) (hsize : (K : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ))
    (hhalf : (K : ℝ) ≤ (n : ℝ) / 2) :
    |Real.log ((n.descFactorial K : ℝ) / (n : ℝ) ^ K) +
      (K : ℝ) ^ 2 / (2 * n) + (K : ℝ) ^ 3 / (6 * (n : ℝ) ^ 2)| ≤
        leadingErrorEnvelope n C := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hr := critical_ratio_bound hn hsize
  have hr0 : (0 : ℝ) ≤ (K : ℝ) / n := by positivity
  have hsq : ((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 = (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnR.le]
    norm_num
  have hinv : (n : ℝ) ^ (-(1 / 3 : ℝ)) / n = (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    have hh := Real.rpow_sub hnR (-(1 / 3 : ℝ)) 1
    norm_num only [Real.rpow_one] at hh
    convert hh.symm using 1
  have h1 : (K : ℝ) / (2 * n) ≤ (C / 2) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    calc
      _ = ((K : ℝ) / n) / 2 := by ring
      _ ≤ (C * (n : ℝ) ^ (-(1 / 3 : ℝ))) / 2 :=
        div_le_div_of_nonneg_right hr (by norm_num)
      _ = _ := by ring
  have h2 : (K : ℝ) ^ 2 / (4 * (n : ℝ) ^ 2) ≤
      (C ^ 2 / 4) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    have hh := pow_le_pow_left₀ hr0 hr 2
    rw [div_pow, mul_pow, hsq] at hh
    calc
      _ = ((K : ℝ) ^ 2 / (n : ℝ) ^ 2) / 4 := by ring
      _ ≤ (C ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) / 4 :=
        div_le_div_of_nonneg_right hh (by norm_num)
      _ = _ := by ring
  have h3 : (K : ℝ) / (12 * (n : ℝ) ^ 2) ≤
      (C / 12) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    have hh := div_le_div_of_nonneg_right hr hnR.le
    rw [mul_div_assoc, hinv] at hh
    have heq : (K : ℝ) / n / n = (K : ℝ) / (n : ℝ) ^ 2 := by ring
    rw [heq] at hh
    calc
      _ = ((K : ℝ) / (n : ℝ) ^ 2) / 12 := by ring
      _ ≤ (C * (n : ℝ) ^ (-(4 / 3 : ℝ))) / 12 :=
        div_le_div_of_nonneg_right hh (by norm_num)
      _ = _ := by ring
  exact (log_selection_leading_error hn hhalf).trans (by
    dsimp only [leadingErrorEnvelope]
    linarith [FinitePopulationLog.fourth_remainder_bound hn hC hsize])

/-- Uniformly over all critical-size integer profiles, real ambient
counts eventually lie in the falling-factorial Taylor domain. -/
theorem eventually_uniform_depletion_domain (M : FiniteIrreducibleModel S)
    (c : ℕ → S → ℕ) (D C : ℝ) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) :
    ∀ᶠ n : ℕ in atTop, (∀ a, 0 < c n a) ∧ ∀ K : S → ℕ,
      (∑ a, (K a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
      ∀ a, (K a : ℝ) ≤ typeScale M C a * (c n a : ℝ) ^ (2 / 3 : ℝ) ∧
        (K a : ℝ) ≤ (c n a : ℝ) / 2 := by
  have he : ∀ᶠ n in atTop, ∀ a,
      typeScale M C a * (c n a : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 := by
    apply eventually_all.mpr
    intro a
    have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp (typeCount_tendsto_atTop M c D hround a))).const_mul
        (typeScale M C a)
    simp only [mul_zero] at ht
    exact (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      (fun _ h ↦ h.le)
  filter_upwards [hround, eventually_count_ratio_domain M c D hround, he] with n hr hd hs
  refine ⟨hd.2.1, ?_⟩
  intro K hsize a
  have hlow : ∀ a, (n : ℝ) * M.weight a / 2 ≤ c n a := by
    intro a
    have hμ := mul_pos (Nat.cast_pos.mpr hd.1 : (0 : ℝ) < n) (M.weight_pos a)
    have hD := (div_le_iff₀ hμ).mp (hd.2.2 a)
    have hh := (abs_le.mp (hr a)).1
    linarith
  have hb := type_critical_size_bound M (c n) K hC hlow hsize a
  refine ⟨hb, ?_⟩
  have hratio := (critical_ratio_bound (hd.2.1 a) hb).trans (hs a)
  have hh := (div_le_iff₀ (Nat.cast_pos.mpr (hd.2.1 a) : (0 : ℝ) < c n a)).mp hratio
  linarith

/-- A genuine all-profile vanishing bound, not only a bound along one
chosen profile sequence. It applies without any probabilistic typicality. -/
theorem normalizedDepletion_uniform_leading_remainder (M : FiniteIrreducibleModel S)
    (c : ℕ → S → ℕ) (D C : ℝ) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ K : S → ℕ,
        (∑ a, (K a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
        0 < normalizedDepletion (c n) K ∧
        |Real.log (normalizedDepletion (c n) K) +
          ∑ a, (K a : ℝ) ^ 2 / (2 * c n a) +
          ∑ a, (K a : ℝ) ^ 3 / (6 * (c n a : ℝ) ^ 2)| ≤ err n := by
  let err : ℕ → ℝ := fun n ↦ ∑ a, leadingErrorEnvelope (c n a) (typeScale M C a)
  have ht : Tendsto err atTop (𝓝 0) := by
    have hs := tendsto_finsetSum Finset.univ (fun a _ ↦
      leadingErrorEnvelope_tendsto_zero (fun n ↦ c n a)
        (typeCount_tendsto_atTop M c D hround a) (typeScale M C a))
    simpa only [Finset.sum_const_zero] using hs
  refine ⟨err, ht, ?_⟩
  filter_upwards [eventually_uniform_depletion_domain M c D C hC hround] with n hn
  intro K hsize
  have hK : ∀ a, K a ≤ c n a := by
    intro a
    have hh := (hn.2 K hsize a).2
    exact_mod_cast (show (K a : ℝ) ≤ c n a by
      linarith [show (0 : ℝ) ≤ c n a from Nat.cast_nonneg (c n a)])
  refine ⟨normalizedDepletion_pos (c n) K hn.1 hK, ?_⟩
  rw [log_normalizedDepletion (c n) K hn.1 hK, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ ↦
    log_selection_leading_error_envelope (hn.1 a) (typeScale_nonneg M hC a)
      (hn.2 K hsize a).1 (hn.2 K hsize a).2))

end PerronWright.FiniteIrreducibleDeterministicDepletion
