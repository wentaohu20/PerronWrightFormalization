import PerronWright.Probability.FiniteIrreduciblePearsonProfile

/-! # Exact Perron cancellation for the actual finite count exponents

Only the genuine finite critical Perron eigenvector identity is used.
Periodicity is unrestricted. The identities apply to arbitrary real
count vectors and hence to every literal pooled component profile.
-/

open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FiniteIrreduciblePerronCountExpansion

open FiniteIrreduciblePearsonProfile (perronMass)

variable {S : Type*} [Fintype S] [DecidableEq S]

def bilinear (M : FiniteIrreducibleModel S) (v w : S → ℝ) : ℝ :=
  ∑ a, ∑ b, v a * M.kernel a b * w b

def weightedSquare (M : FiniteIrreducibleModel S) (v : S → ℝ) : ℝ :=
  ∑ a, (v a) ^ 2 / M.weight a

def weightedCube (M : FiniteIrreducibleModel S) (v : S → ℝ) : ℝ :=
  ∑ a, (v a) ^ 3 / (M.weight a) ^ 2

def deviation (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) (a : S) : ℝ := v a - K * perronMass M hM a

theorem bilinear_symm (M : FiniteIrreducibleModel S) (v w : S → ℝ) :
    bilinear M v w = bilinear M w v := by
  unfold bilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [M.symmetric b a]
  ring

theorem perron_kernel_sum (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (a : S) :
    (∑ b, M.kernel a b * perronMass M hM b) = M.perronFunction hM a := by
  have hf := congrFun (M.perronFunction_fixed hM) a
  simpa only [FiniteIrreducibleModel.action, perronMass, mul_assoc] using hf

theorem bilinear_perron_right (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (v : S → ℝ) :
    bilinear M v (perronMass M hM) = ∑ a, v a * M.perronFunction hM a := by
  unfold bilinear
  simp only [mul_assoc, ← Finset.mul_sum, perron_kernel_sum]

theorem bilinear_perron_left (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (v : S → ℝ) :
    bilinear M (perronMass M hM) v = ∑ a, v a * M.perronFunction hM a := by
  rw [bilinear_symm, bilinear_perron_right]

theorem bilinear_perron (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    bilinear M (perronMass M hM) (perronMass M hM) = M.alpha hM := by
  rw [bilinear_perron_right]
  unfold FiniteIrreducibleModel.alpha FiniteIrreducibleModel.average perronMass
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem bilinear_affine (M : FiniteIrreducibleModel S) (K : ℝ) (p d : S → ℝ) :
    bilinear M (fun a ↦ K * p a + d a) (fun a ↦ K * p a + d a) =
      K ^ 2 * bilinear M p p + 2 * K * bilinear M d p + bilinear M d d := by
  have hexp : bilinear M (fun a ↦ K * p a + d a) (fun a ↦ K * p a + d a) =
      K ^ 2 * bilinear M p p + K * bilinear M p d + K * bilinear M d p + bilinear M d d := by
    unfold bilinear
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hexp, bilinear_symm M p d]
  ring

/-- The large K² and linear profile terms in the isolation quadratic. -/
theorem quadratic_perron_expansion (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) :
    bilinear M v v = M.alpha hM * K ^ 2 +
      2 * K * (∑ a, deviation M hM K v a * M.perronFunction hM a) +
        bilinear M (deviation M hM K v) (deviation M hM K v) := by
  have hv : v = fun a ↦ K * perronMass M hM a + deviation M hM K v a := by
    funext a
    unfold deviation
    ring
  calc
    _ = bilinear M (fun a ↦ K * perronMass M hM a + deviation M hM K v a)
        (fun a ↦ K * perronMass M hM a + deviation M hM K v a) := by rw [← hv]
    _ = _ := by rw [bilinear_affine, bilinear_perron, bilinear_perron_right]; ring

/-- The same large K² and linear terms in literal type depletion. -/
theorem square_perron_expansion (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) :
    weightedSquare M v = M.alpha hM * K ^ 2 +
      2 * K * (∑ a, deviation M hM K v a * M.perronFunction hM a) +
        weightedSquare M (deviation M hM K v) := by
  unfold weightedSquare FiniteIrreducibleModel.alpha FiniteIrreducibleModel.average
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  unfold deviation perronMass
  field_simp [(M.weight_pos a).ne']
  ring

/-- The literal cubic depletion exponent, with each fluctuation term
retained exactly instead of assuming a typical-profile replacement. -/
theorem cube_perron_expansion (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) :
    weightedCube M v = M.beta hM * K ^ 3 +
      3 * K ^ 2 * (∑ a, deviation M hM K v a * (M.perronFunction hM a) ^ 2) +
      3 * K * (∑ a, M.perronFunction hM a * (deviation M hM K v a) ^ 2 / M.weight a) +
        weightedCube M (deviation M hM K v) := by
  unfold weightedCube FiniteIrreducibleModel.beta FiniteIrreducibleModel.average
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  unfold deviation perronMass
  field_simp [(M.weight_pos a).ne']
  ring

/-- Exact cancellation of the two potentially divergent quadratic
profile terms. This needs irreducible criticality, not positive powers. -/
theorem quadratic_depletion_isolation_cancellation (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (K t : ℝ) (v : S → ℝ) :
    t * bilinear M v v - weightedSquare M v =
      M.alpha hM * (t - 1) * K ^ 2 +
      2 * (t - 1) * K * (∑ a, deviation M hM K v a * M.perronFunction hM a) +
      t * bilinear M (deviation M hM K v) (deviation M hM K v) -
        weightedSquare M (deviation M hM K v) := by
  rw [quadratic_perron_expansion M hM K v, square_perron_expansion M hM K v]
  ring

def mainExponent (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (n K t : ℝ) : ℝ := M.alpha hM * (t - 1) * K ^ 2 / (2 * n) -
      M.beta hM * K ^ 3 / (6 * n ^ 2)

def isolationCore (M : FiniteIrreducibleModel S) (n t : ℝ) (v : S → ℝ) : ℝ :=
  t * bilinear M v v / (2 * n) - weightedSquare M v / (2 * n) -
    weightedCube M v / (6 * n ^ 2)

theorem isolationCore_sub_main (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (n K t : ℝ) (v : S → ℝ) :
    isolationCore M n t v - mainExponent M hM n K t =
      ((t - 1) * K / n) * (∑ a, deviation M hM K v a * M.perronFunction hM a) +
      (t * bilinear M (deviation M hM K v) (deviation M hM K v) -
        weightedSquare M (deviation M hM K v)) / (2 * n) -
      (K ^ 2 / (2 * n ^ 2)) * (∑ a, deviation M hM K v a * (M.perronFunction hM a) ^ 2) -
      (K / (2 * n ^ 2)) *
        (∑ a, M.perronFunction hM a * (deviation M hM K v a) ^ 2 / M.weight a) -
      weightedCube M (deviation M hM K v) / (6 * n ^ 2) := by
  unfold isolationCore mainExponent
  rw [quadratic_perron_expansion M hM K v, square_perron_expansion M hM K v,
    cube_perron_expansion M hM K v]
  ring

def countPearson (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) : ℝ :=
  ∑ a, (deviation M hM K v a) ^ 2 / perronMass M hM a

theorem countPearson_nonneg (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) : 0 ≤ countPearson M hM K v :=
  Finset.sum_nonneg (fun a _ ↦ div_nonneg (sq_nonneg _)
    (FiniteIrreduciblePearsonProfile.perronMass_pos M hM a).le)

theorem perronMass_sum (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∑ a, perronMass M hM a = 1 := M.perronFunction_average hM

theorem perronMass_le_one (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (a : S) :
    perronMass M hM a ≤ 1 := by
  rw [← perronMass_sum M hM]
  exact Finset.single_le_sum
    (fun b _ ↦ (FiniteIrreduciblePearsonProfile.perronMass_pos M hM b).le) (Finset.mem_univ a)

theorem deviation_sq_le_pearson (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) (a : S) :
    (deviation M hM K v a) ^ 2 ≤ countPearson M hM K v := by
  have hp := FiniteIrreduciblePearsonProfile.perronMass_pos M hM a
  calc
    _ ≤ (deviation M hM K v a) ^ 2 / perronMass M hM a := by
      apply (le_div_iff₀ hp).mpr
      exact mul_le_of_le_one_right (sq_nonneg _) (perronMass_le_one M hM a)
    _ ≤ _ := Finset.single_le_sum
      (f := fun b ↦ (deviation M hM K v b) ^ 2 / perronMass M hM b)
      (fun b _ ↦ div_nonneg (sq_nonneg _) (FiniteIrreduciblePearsonProfile.perronMass_pos M hM b).le)
      (Finset.mem_univ a)

theorem sum_deviation_sq_le_pearson (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) :
    (∑ a, (deviation M hM K v a) ^ 2) ≤ countPearson M hM K v := by
  apply Finset.sum_le_sum
  intro a _
  apply (le_div_iff₀ (FiniteIrreduciblePearsonProfile.perronMass_pos M hM a)).mpr
  exact mul_le_of_le_one_right (sq_nonneg _) (perronMass_le_one M hM a)

theorem deviation_abs_le_total (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (K : ℝ) (v : S → ℝ) (hv : ∀ a, 0 ≤ v a) (hs : ∑ a, v a = K) (a : S) :
    |deviation M hM K v a| ≤ K := by
  have hK : 0 ≤ K := hs ▸ Finset.sum_nonneg (fun b _ ↦ hv b)
  have hcount : v a ≤ K := hs ▸ Finset.single_le_sum (fun b _ ↦ hv b) (Finset.mem_univ a)
  have hp : 0 ≤ perronMass M hM a := (FiniteIrreduciblePearsonProfile.perronMass_pos M hM a).le
  have hpK : K * perronMass M hM a ≤ K := mul_le_of_le_one_right hK (perronMass_le_one M hM a)
  rw [abs_le]
  unfold deviation
  constructor <;> nlinarith [hv a, mul_nonneg hK hp]

end PerronWright.FiniteIrreduciblePerronCountExpansion
