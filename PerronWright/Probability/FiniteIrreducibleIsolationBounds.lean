import PerronWright.Probability.FiniteIrreduciblePerronCountExpansion
import PerronWright.Probability.CriticalScaling

/-! # Proved Pearson domination of finite isolation fluctuations

The bounds cover every nonnegative literal count vector with the stated
total size. No typical-profile event, Gaussian-tail extension, or
quadratic uniform-integrability premise is introduced.
-/

open Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FiniteIrreducibleIsolationBounds

open FiniteIrreduciblePerronCountExpansion

variable {S : Type*} [Fintype S] [DecidableEq S]

def kernelBudget (M : FiniteIrreducibleModel S) : ℝ := ∑ a, ∑ b, |M.kernel a b|
def squareBudget (M : FiniteIrreducibleModel S) : ℝ := ∑ a, (M.weight a)⁻¹
def cubeBudget (M : FiniteIrreducibleModel S) : ℝ := ∑ a, ((M.weight a) ^ 2)⁻¹
def cubicSquareBudget (M : FiniteIrreducibleModel S) (hM : M.IsCritical) : ℝ :=
  ∑ a, |M.perronFunction hM a| / M.weight a
def linearBudget (f : S → ℝ) : ℝ := ∑ a, (f a) ^ 2

theorem budgets_nonneg (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    0 ≤ kernelBudget M ∧ 0 ≤ squareBudget M ∧ 0 ≤ cubeBudget M ∧
      0 ≤ cubicSquareBudget M hM := by
  refine ⟨Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ abs_nonneg _)),
    Finset.sum_nonneg (fun a _ ↦ (inv_pos.mpr (M.weight_pos a)).le),
    Finset.sum_nonneg (fun a _ ↦ (inv_pos.mpr (sq_pos_of_pos (M.weight_pos a))).le),
    Finset.sum_nonneg (fun a _ ↦ div_nonneg (abs_nonneg _) (M.weight_pos a).le)⟩

theorem deviation_bilinear_abs_le (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) :
    |bilinear M (deviation M hM K v) (deviation M hM K v)| ≤
      kernelBudget M * countPearson M hM K v := by
  let d := deviation M hM K v
  let V := countPearson M hM K v
  have hproduct (a b : S) : |d a| * |d b| ≤ V := by
    have ha := deviation_sq_le_pearson M hM K v a
    have hb := deviation_sq_le_pearson M hM K v b
    dsimp only [d, V]
    nlinarith [sq_nonneg (|d a| - |d b|), sq_abs (d a), sq_abs (d b)]
  unfold bilinear kernelBudget
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro a _
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro b _
  rw [abs_mul, abs_mul]
  calc
    _ = |M.kernel a b| * (|d a| * |d b|) := by dsimp only [d]; ring
    _ ≤ |M.kernel a b| * V := mul_le_mul_of_nonneg_left (hproduct a b) (abs_nonneg _)

theorem deviation_square_abs_le (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) :
    |weightedSquare M (deviation M hM K v)| ≤ squareBudget M * countPearson M hM K v := by
  unfold weightedSquare squareBudget
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro a _
  rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (M.weight_pos a)]
  exact (div_le_div_of_nonneg_right (deviation_sq_le_pearson M hM K v a)
    (M.weight_pos a).le).trans_eq (by ring)

theorem deviation_cubic_square_abs_le (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) :
    |∑ a, M.perronFunction hM a * (deviation M hM K v a) ^ 2 / M.weight a| ≤
      cubicSquareBudget M hM * countPearson M hM K v := by
  unfold cubicSquareBudget
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro a _
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (deviation M hM K v a)),
    abs_of_pos (M.weight_pos a)]
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (deviation_sq_le_pearson M hM K v a) (abs_nonneg _))
      (M.weight_pos a).le).trans_eq (by ring)

theorem deviation_cube_abs_le (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) (hv : ∀ a, 0 ≤ v a) (hs : ∑ a, v a = K) :
    |weightedCube M (deviation M hM K v)| ≤
      K * cubeBudget M * countPearson M hM K v := by
  have hK : 0 ≤ K := hs ▸ Finset.sum_nonneg (fun a _ ↦ hv a)
  unfold weightedCube cubeBudget
  rw [mul_comm K, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro a _
  have hh := mul_le_mul (deviation_abs_le_total M hM K v hv hs a)
    (deviation_sq_le_pearson M hM K v a) (sq_nonneg _) hK
  have heq : |(deviation M hM K v a) ^ 3| =
      |deviation M hM K v a| * (deviation M hM K v a) ^ 2 := by
    rw [pow_succ, abs_mul, abs_of_nonneg (sq_nonneg _)]
    ring
  rw [abs_div, heq, abs_of_pos (sq_pos_of_pos (M.weight_pos a))]
  exact (div_le_div_of_nonneg_right hh (sq_pos_of_pos (M.weight_pos a)).le).trans_eq (by ring)

theorem scalar_young_bound {n x c f : ℝ} (hn : 0 < n) :
    |c * x * f| ≤ x ^ 2 / n + n * c ^ 2 * f ^ 2 := by
  have heq : x ^ 2 / n + n * c ^ 2 * f ^ 2 = (x ^ 2 + n ^ 2 * c ^ 2 * f ^ 2) / n := by
    field_simp
  rw [heq]
  apply (le_div_iff₀ hn).mpr
  have heq' : |c * x * f| * n = |n * c * x * f| := by
    simp only [abs_mul, abs_of_pos hn]
    ring
  rw [heq']
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (x - n * c * f), sq_nonneg (x + n * c * f)]

theorem deviation_linear_young_bound (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v f : S → ℝ) {n : ℝ} (hn : 0 < n) (c : ℝ) :
    |c * (∑ a, deviation M hM K v a * f a)| ≤
      countPearson M hM K v / n + n * c ^ 2 * linearBudget f := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ a, |c * (deviation M hM K v a * f a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ((deviation M hM K v a) ^ 2 / n + n * c ^ 2 * (f a) ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [mul_assoc] using scalar_young_bound (x := deviation M hM K v a) (c := c) (f := f a) hn
    _ = (∑ a, (deviation M hM K v a) ^ 2) / n + n * c ^ 2 * linearBudget f := by
      rw [Finset.sum_add_distrib, Finset.sum_div, ← Finset.mul_sum]
      rfl
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_right (sum_deviation_sq_le_pearson M hM K v) hn.le) le_rfl

def isolationBudget (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (C T : ℝ) : ℝ :=
  2 + (T * kernelBudget M + squareBudget M) / 2 +
    C * cubicSquareBudget M hM / 2 + C * cubeBudget M / 6

theorem isolationBudget_nonneg (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) :
    0 ≤ isolationBudget M hM C T := by
  obtain ⟨hκ, hw, hcube, hcs⟩ := budgets_nonneg M hM
  unfold isolationBudget
  positivity

/-- All nonlinear deviations are genuinely dominated by the Pearson
statistic; the two linear deviations have explicit Young remainders. -/
theorem isolationCore_error_bound (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n K t C T : ℝ} (hn : 0 < n) (_hC : 0 ≤ C) (hT : 0 ≤ T)
    (ht : |t| ≤ T) (v : S → ℝ) (hv : ∀ a, 0 ≤ v a) (hs : ∑ a, v a = K)
    (hsize : K ≤ C * n) :
    |isolationCore M n t v - mainExponent M hM n K t| ≤
      isolationBudget M hM C T * countPearson M hM K v / n +
      n * (((t - 1) * K / n) ^ 2) * linearBudget (M.perronFunction hM) +
      n * ((K ^ 2 / (2 * n ^ 2)) ^ 2) * linearBudget (fun a ↦ (M.perronFunction hM a) ^ 2) := by
  let d := deviation M hM K v
  let V := countPearson M hM K v
  have hV : 0 ≤ V := countPearson_nonneg M hM K v
  have hK : 0 ≤ K := hs ▸ Finset.sum_nonneg (fun a _ ↦ hv a)
  obtain ⟨hκ, hw, hcube, hcs⟩ := budgets_nonneg M hM
  have hq : |(t * bilinear M d d - weightedSquare M d) / (2 * n)| ≤
      (T * kernelBudget M + squareBudget M) * V / (2 * n) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * n)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    refine (abs_sub _ _).trans ?_
    have hh : |t * bilinear M d d| ≤ T * (kernelBudget M * V) := by
      rw [abs_mul]
      exact mul_le_mul ht (deviation_bilinear_abs_le M hM K v) (abs_nonneg _) hT
    have hw' := deviation_square_abs_le M hM K v
    exact (add_le_add hh hw').trans_eq (by dsimp only [d, V]; ring)
  have hcs' : |(K / (2 * n ^ 2)) *
      (∑ a, M.perronFunction hM a * (d a) ^ 2 / M.weight a)| ≤
      C * cubicSquareBudget M hM * V / (2 * n) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ K / (2 * n ^ 2))]
    have hb := mul_le_mul_of_nonneg_left (deviation_cubic_square_abs_le M hM K v)
      (by positivity : 0 ≤ K / (2 * n ^ 2))
    refine hb.trans ?_
    calc
      _ ≤ (C * n / (2 * n ^ 2)) * (cubicSquareBudget M hM * V) := by gcongr
      _ = _ := by field_simp
  have hcube' : |weightedCube M d / (6 * n ^ 2)| ≤
      C * cubeBudget M * V / (6 * n) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 6 * n ^ 2)]
    refine (div_le_div_of_nonneg_right (deviation_cube_abs_le M hM K v hv hs)
      (by positivity)).trans ?_
    calc
      _ ≤ (C * n) * cubeBudget M * V / (6 * n ^ 2) := by gcongr
      _ = _ := by field_simp
  have hlin := deviation_linear_young_bound M hM K v (M.perronFunction hM) hn ((t - 1) * K / n)
  have hlin2 := deviation_linear_young_bound M hM K v
    (fun a ↦ (M.perronFunction hM a) ^ 2) hn (K ^ 2 / (2 * n ^ 2))
  rw [isolationCore_sub_main]
  have triangle (a b c d e : ℝ) :
      |a + b - c - d - e| ≤ |a| + |b| + |c| + |d| + |e| :=
    (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
      (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  refine (triangle _ _ _ _ _).trans ?_
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add hlin hq) hlin2) hcs') hcube'
  refine hsum.trans_eq ?_
  dsimp only [isolationBudget, V]
  ring

def criticalLinearEnvelope (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda C : ℝ) (n : ℕ) : ℝ :=
  (lambda ^ 2 * C ^ 2 * linearBudget (M.perronFunction hM) +
    (C ^ 4 / 4) * linearBudget (fun a ↦ (M.perronFunction hM a) ^ 2)) *
      (n : ℝ) ^ (-(1 / 3 : ℝ))

theorem criticalLinearEnvelope_tendsto_zero (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda C : ℝ) : Tendsto (criticalLinearEnvelope M hM lambda C) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦
    (lambda ^ 2 * C ^ 2 * linearBudget (M.perronFunction hM) +
      (C ^ 4 / 4) * linearBudget (fun a ↦ (M.perronFunction hM a) ^ 2)) *
        (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0)
  have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    tendsto_natCast_atTop_atTop).const_mul
      (lambda ^ 2 * C ^ 2 * linearBudget (M.perronFunction hM) +
        (C ^ 4 / 4) * linearBudget (fun a ↦ (M.perronFunction hM a) ^ 2))
  simpa only [Function.comp_def, mul_zero, criticalLinearEnvelope] using ht

theorem critical_linear_remainder_bound {n : ℕ} (hn : 0 < n) {K C lambda : ℝ}
    (hK : 0 ≤ K) (hsize : K ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    (n : ℝ) * ((lambda * (n : ℝ) ^ (-(1 / 3 : ℝ)) * K / n) ^ 2) ≤
      lambda ^ 2 * C ^ 2 * (n : ℝ) ^ (-(1 / 3 : ℝ)) ∧
    (n : ℝ) * ((K ^ 2 / (2 * (n : ℝ) ^ 2)) ^ 2) ≤
      (C ^ 4 / 4) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hscale2 : ((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 *
      ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 / n = (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have hprod : ((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 *
        ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = (n : ℝ) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnR.le,
        ← Real.rpow_natCast _ 2, ← Real.rpow_mul hnR.le, ← Real.rpow_add hnR]
      norm_num
    rw [hprod]
    have hh := Real.rpow_sub hnR (2 / 3 : ℝ) 1
    norm_num only [Real.rpow_one] at hh
    convert hh.symm using 1
  have hscale4 : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 4 / (n : ℝ) ^ 3 =
      (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hnR.le,
      ← Real.rpow_natCast _ 3, ← Real.rpow_sub hnR]
    norm_num
  constructor
  · calc
      _ = (lambda ^ 2 * ((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2) * K ^ 2 / n := by field_simp
      _ ≤ (lambda ^ 2 * ((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2) *
          (C * (n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 / n := by gcongr
      _ = lambda ^ 2 * C ^ 2 *
          (((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 * ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 / n) := by ring
      _ = _ := by rw [hscale2]
  · calc
      _ = K ^ 4 / (4 * (n : ℝ) ^ 3) := by field_simp; norm_num
      _ ≤ (C * (n : ℝ) ^ (2 / 3 : ℝ)) ^ 4 / (4 * (n : ℝ) ^ 3) := by gcongr
      _ = (C ^ 4 / 4) * (((n : ℝ) ^ (2 / 3 : ℝ)) ^ 4 / (n : ℝ) ^ 3) := by ring
      _ = _ := by rw [hscale4]

/-- A concrete all-profile bound at the paper's actual critical time.
The only nonvanishing random control is the already proved Pearson/n
exponential moment. The displayed deterministic envelope tends to zero. -/
theorem eventually_uniform_critical_isolation_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ K : ℝ, ∀ v : S → ℝ,
      (∀ a, 0 ≤ v a) → (∑ a, v a = K) → K ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
      |isolationCore M (n : ℝ) (CriticalScaling.time lambda n) v -
        mainExponent M hM (n : ℝ) K (CriticalScaling.time lambda n)| ≤
      (isolationBudget M hM C 2 / (n : ℝ)) * countPearson M hM K v +
        criticalLinearEnvelope M hM lambda C n := by
  have ht : ∀ᶠ n in atTop, |CriticalScaling.time lambda n| ≤ 2 := by
    have hh := (CriticalScaling.time_tendsto lambda).abs
    simp only [abs_one] at hh
    exact (hh.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))).mono (fun _ h ↦ h.le)
  filter_upwards [ht, CriticalScaling.time_eq_raw_eventually lambda,
    eventually_ge_atTop (1 : ℕ)] with n htn hraw hn1
  intro K v hv hs hsize
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hK : 0 ≤ K := hs ▸ Finset.sum_nonneg (fun a _ ↦ hv a)
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hs' : K ≤ C * (n : ℝ) := hsize.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num : (2 / 3 : ℝ) ≤ 1)) hC)
  have hb := isolationCore_error_bound M hM hnR hC (by norm_num) htn v hv hs hs'
  have hlin := critical_linear_remainder_bound hn hK hsize (lambda := lambda)
  have heq : CriticalScaling.time lambda n - 1 = lambda * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [hraw]
    ring
  rw [heq] at hb
  have hφ : 0 ≤ linearBudget (M.perronFunction hM) := Finset.sum_nonneg (fun a _ ↦ sq_nonneg _)
  have hφ4 : 0 ≤ linearBudget (fun a ↦ (M.perronFunction hM a) ^ 2) :=
    Finset.sum_nonneg (fun a _ ↦ sq_nonneg _)
  refine hb.trans ?_
  have h1 := mul_le_mul_of_nonneg_right hlin.1 hφ
  have h2 := mul_le_mul_of_nonneg_right hlin.2 hφ4
  exact (add_le_add (add_le_add le_rfl h1) h2).trans_eq (by
    dsimp only [criticalLinearEnvelope]
    ring)

end PerronWright.FiniteIrreducibleIsolationBounds
