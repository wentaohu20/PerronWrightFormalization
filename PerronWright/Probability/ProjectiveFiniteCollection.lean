import PerronWright.Probability.ProfileFiniteCollection
import PerronWright.Probability.ProjectiveExponential
import PerronWright.Probability.ProfileScaleMatched

/-! # Genuine pooled empirical projective statistics under product laws -/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.ProjectiveFiniteCollection

open ConnectedTypeLaw ProfileSquareMoment ProfileSquareSeries
open ProfileFiniteCollection ProjectiveKernel ProjectiveExponential

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- All actual sampled types in the pooled vertex set. -/
def pooledTypes {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) :
    Fin (Fintype.card ((i : Fin q) × Fin (k i))) → S := fun v ↦
  let w := (Fintype.equivFin ((i : Fin q) × Fin (k i))).symm v
  (p w.1).1 w.2

theorem pooled_card {q : ℕ} (k : Fin q → ℕ) :
    Fintype.card ((i : Fin q) × Fin (k i)) = ∑ i, k i := by
  simp

theorem pooled_card_real {q : ℕ} (k : Fin q → ℕ) :
    (Fintype.card ((i : Fin q) × Fin (k i)) : ℝ) = ∑ i, (k i : ℝ) := by
  rw [pooled_card, Nat.cast_sum]

theorem pooled_card_pos {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    0 < Fintype.card ((i : Fin q) × Fin (k i)) := by
  have hpos := totalSize_pos hq k hk
  rw [← pooled_card_real] at hpos
  exact_mod_cast hpos

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem typeSum_pooledTypes {q : ℕ} (k : Fin q → ℕ) (f : C(S, ℝ))
    (p : StateFamily (S := S) k) :
    typeSum f (pooledTypes k p) = ∑ i, typeSum f (p i).1 := by
  unfold typeSum pooledTypes
  calc
    _ = ∑ w : (i : Fin q) × Fin (k i), f ((p w.1).1 w.2) :=
      Equiv.sum_comp (Fintype.equivFin ((i : Fin q) × Fin (k i))).symm
        (fun w ↦ f ((p w.1).1 w.2))
    _ = _ := Fintype.sum_sigma _

theorem centeredSum_pooledTypes (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (k : Fin q → ℕ) (f : C(S, ℝ)) (p : StateFamily (S := S) k) :
    ProfileLaplace.centeredSum M hM f (pooledTypes k p, ⊥) =
      ∑ i, ProfileLaplace.centeredSum M hM f (p i) := by
  simp only [ProfileLaplace.centeredSum, typeSum_pooledTypes, Finset.sum_sub_distrib,
    ← Finset.sum_mul, pooled_card_real]

/-- The genuine double-integral empirical quadratic of all sampled
vertices in the collection, with no feature-series definition substituted. -/
def pooledQuadratic (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (H : C(S × S, ℝ)) (p : StateFamily (S := S) k) : ℝ := by
  let : NeZero (Fintype.card ((i : Fin q) × Fin (k i))) :=
    ⟨(pooled_card_pos hq k hk).ne'⟩
  exact empiricalQuadratic M hM (pooledTypes k p) Finset.univ Finset.univ_nonempty H

theorem pooledQuadratic_eq_tsum (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) (p : StateFamily (S := S) k) :
    pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p =
      ∑' j, a j * (pooledSum M hM k (f j) p) ^ 2 := by
  have hkpos := pooled_card_pos hq k hk
  have he := componentQuadratic_eq_tsum M hM hkpos hs (pooledTypes k p, ⊥)
  change pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p = _ at he
  simp_rw [scaledSum, centeredSum_pooledTypes, pooled_card_real] at he
  exact he

theorem pooledQuadratic_abs_le_feature_sum (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) (p : StateFamily (S := S) k) :
    |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p| ≤
      ∑' j, |a j| * (pooledSum M hM k (f j) p) ^ 2 := by
  have he := componentQuadratic_abs_le_feature_sum M hM (pooled_card_pos hq k hk) hs
    (pooledTypes k p, ⊥)
  change |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p| ≤ _ at he
  simp_rw [scaledSum, centeredSum_pooledTypes, pooled_card_real] at he
  exact he

theorem pooledQuadratic_abs_le_budget (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) {B : ℝ}
    (hbudget : ∑' j, |a j| * ‖f j‖ ^ 2 ≤ B) (p : StateFamily (S := S) k) :
    |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p| ≤
      4 * (∑ i, (k i : ℝ)) * B := by
  have he := componentQuadratic_abs_le_budget M hM (pooled_card_pos hq k hk) hs hbudget
    (pooledTypes k p, ⊥)
  change |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p| ≤ _ at he
  simpa only [pooled_card_real] using he

theorem pooledQuadratic_measurable_of_representation (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) :
    Measurable (pooledQuadratic M hM hq k hk (∑' j, a j • square (f j))) := by
  have he : pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) =
      fun p ↦ ∑' j, a j * (pooledSum M hM k (f j) p) ^ 2 := by
    funext p
    exact pooledQuadratic_eq_tsum M hM hq k hk hs p
  rw [he]
  exact Measurable.tsum (fun j ↦ ((pooledSum_measurable M hM k (f j)).pow_const 2).const_mul _)

theorem integrable_exp_pooledQuadratic (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {q : ℕ} (hq : 0 < q) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (g : Fin q → C(S, ℝ))
    (hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i))
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) (γ : ℝ) (hγ : 0 ≤ γ) :
    Integrable (fun p ↦ Real.exp (γ *
      |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p|))
        (productLaw M k r g hC) := by
  have habs : Measurable (fun p : StateFamily (S := S) k ↦
      |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p|) := by
    simpa only [Real.norm_eq_abs] using (pooledQuadratic_measurable_of_representation M hM hq k hk hs).norm
  apply integrable_of_measurable_abs_le (productLaw M k r g hC)
    (B := Real.exp (γ * (4 * (∑ i, (k i : ℝ)) * ∑' j, |a j| * ‖f j‖ ^ 2)))
    (habs.const_mul _).exp
  intro p
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (pooledQuadratic_abs_le_budget M hM hq k hk hs le_rfl p) hγ)

/-- Projective exponential control for a genuine pooled empirical law
under the literal product of the connected component laws. -/
theorem exists_uniform_pooledQuadratic_exponential_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R q : ℕ) (hq : 0 < q) (L A B : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ k r : Fin q → ℕ, ∀ hk : ∀ i, 0 < k i,
      (∀ i, r i ≤ R) → ∀ g : Fin q → C(S, ℝ), (∀ i, Real.sqrt (k i : ℝ) * ‖g i‖ ≤ L) →
      ∀ (a : ℕ → ℝ) (f : ℕ → C(S, ℝ)),
        Summable (fun j ↦ |a j| * ‖f j‖ ^ 2) → (∑' j, |a j| * ‖f j‖ ^ 2) ≤ B →
      ∀ hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i),
      0 ≤ (∫ p, Real.exp ((A / Real.sqrt (∑ i, (k i : ℝ))) *
          |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p|)
            ∂productLaw M k r g hC) - 1 ∧
        (∫ p, Real.exp ((A / Real.sqrt (∑ i, (k i : ℝ))) *
          |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p|)
            ∂productLaw M k r g hC) - 1 ≤ D / Real.sqrt (∑ i, (k i : ℝ)) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_pooled_feature_square_series_bound M hM R q hq L A B hL hA hB
  refine ⟨D, hD, ?_⟩
  intro k r hk hr g hg a f hs hbudget hC
  have hsqrt : 0 < Real.sqrt (∑ i, (k i : ℝ)) := Real.sqrt_pos.mpr (totalSize_pos hq k hk)
  have he := hbound k r hk hr g hg (fun j ↦ |a j|) f (fun j ↦ abs_nonneg _) hs hbudget hC
  have hi := integrable_exp_pooledQuadratic M hM hq k r hk g hC hs
    (A / Real.sqrt (∑ i, (k i : ℝ))) (by positivity)
  have hsabs : Summable (fun j ↦ abs (abs (a j)) * ‖f j‖ ^ 2) := by simpa only [abs_abs] using hs
  have hiseries := integrable_exp_pooledQuadratic M hM hq k r hk g hC hsabs
    (A / Real.sqrt (∑ i, (k i : ℝ))) (by positivity)
  simp_rw [pooledQuadratic_eq_tsum M hM hq k hk hsabs,
    abs_of_nonneg (tsum_nonneg (fun j ↦ mul_nonneg (abs_nonneg (a j)) (sq_nonneg _)))] at hiseries
  have hu := integral_mono hi hiseries (fun p ↦ Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (pooledQuadratic_abs_le_feature_sum M hM hq k hk hs p)
      (by positivity)))
  have hl := integral_mono (integrable_const (1 : ℝ)) hi
    (fun p ↦ Real.one_le_exp_iff.mpr (by positivity))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hl
  exact ⟨by linarith, by linarith [he.2]⟩

end PerronWright.ProjectiveFiniteCollection
