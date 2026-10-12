import PerronWright.Probability.FiniteIrreducibleProfileFiniteCollection
import PerronWright.Probability.ProfileSquareSeries
import PerronWright.Probability.ProfileScaleMatched

/-! # Actual finite Perron coordinate counts and Pearson exponential control

Every fluctuation is a literal integer vertex-type count minus its
canonical Perron mean. Actual independently sampled connected states
supply the probability law. No Pearson moment or UI interface is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology Real
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreduciblePearsonProfile

open FiniteIrreducibleConnectedTypeLaw (State law perronLaw integral_perronLaw)
open FiniteIrreducibleProfileLaplace (centeredSum eventually_all_field_normalizers_pos)
open FiniteIrreducibleProfileFiniteCollection

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def coordinateTest (a : S) : C(S, ℝ) :=
  ⟨fun x ↦ if x = a then 1 else 0, continuous_of_discreteTopology⟩

omit [MeasurableSpace S] [BorelSpace S] in
theorem norm_coordinateTest_le (a : S) : ‖coordinateTest a‖ ≤ 1 := by
  apply (ContinuousMap.norm_le (coordinateTest a) (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro x
  simp only [coordinateTest, ContinuousMap.coe_mk]
  split_ifs <;> norm_num

def perronMass (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (a : S) : ℝ :=
  M.weight a * M.perronFunction hM a

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem perronMass_pos (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (a : S) :
    0 < perronMass M hM a := mul_pos (M.weight_pos a) (M.perronFunction_pos hM a)

theorem coordinateTest_perron_integral (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (a : S) :
    (∫ x, coordinateTest a x ∂(perronLaw M hM : Measure S)) = perronMass M hM a := by
  rw [integral_perronLaw]
  simp [coordinateTest, perronMass]

omit [Fintype S] [MeasurableSpace S] [BorelSpace S] in
theorem coordinateTest_typeSum {k : ℕ} (a : S) (x : Fin k → S) :
    ConnectedTypeLaw.typeSum (coordinateTest a) x =
      ((Finset.univ.filter (fun v ↦ x v = a)).card : ℝ) := by
  simp [ConnectedTypeLaw.typeSum, coordinateTest]

/-- Aggregate literal vertex-type count in the independent components. -/
def aggregateCount {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) (a : S) : ℕ :=
  ∑ i, (Finset.univ.filter (fun v ↦ (p i).1 v = a)).card

def fluctuation (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ}
    (k : Fin q → ℕ) (p : StateFamily (S := S) k) (a : S) : ℝ :=
  (aggregateCount k p a : ℝ) - (∑ i, (k i : ℝ)) * perronMass M hM a

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem sum_aggregateCount {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) :
    (∑ a, aggregateCount k p a) = ∑ i, k i := by
  unfold aggregateCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simpa using (Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin (k i))) (Finset.univ : Finset S) ((p i).1))

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem sum_aggregateCount_real {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) :
    (∑ a, (aggregateCount k p a : ℝ)) = ∑ i, (k i : ℝ) := by
  exact_mod_cast sum_aggregateCount k p

theorem pooledSum_coordinate (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) (a : S) :
    pooledSum M hM k (coordinateTest a) p =
      fluctuation M hM k p a / Real.sqrt (∑ i, (k i : ℝ)) := by
  simp only [pooledSum, centeredSum, coordinateTest_typeSum, coordinateTest_perron_integral,
    fluctuation, aggregateCount, Nat.cast_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]

def pearson (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ}
    (k : Fin q → ℕ) (p : StateFamily (S := S) k) : ℝ :=
  ∑ a, (fluctuation M hM k p a) ^ 2 / perronMass M hM a

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem pearson_nonneg (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) :
    0 ≤ pearson M hM k p :=
  Finset.sum_nonneg (fun a _ ↦ div_nonneg (sq_nonneg _) (perronMass_pos M hM a).le)

theorem pearson_eq_coordinate_squares (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (p : StateFamily (S := S) k) :
    pearson M hM k p = (∑ i, (k i : ℝ)) *
      ∑ a, (perronMass M hM a)⁻¹ * (pooledSum M hM k (coordinateTest a) p) ^ 2 := by
  have hK := totalSize_pos hq k hk
  have hs := Real.sqrt_pos.mpr hK
  have hsq := Real.sq_sqrt hK.le
  unfold pearson
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [pooledSum_coordinate]
  field_simp [hs.ne', (perronMass_pos M hM a).ne']
  rw [hsq]

/-- A proved quantitative moment bound for the literal Pearson count
statistic under genuine independent connected laws, with all sizes covered. -/
theorem exists_uniform_pearson_square_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q) (L A : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ k r : Fin q → ℕ, (∀ i, 0 < k i) → (∀ i, r i ≤ R) →
      ∀ g : Fin q → C(S, ℝ), (∀ i, Real.sqrt (k i : ℝ) * ‖g i‖ ≤ L) →
      ∀ a : ℝ, 0 ≤ a → a ≤ A →
      ∀ hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i),
      0 ≤ (∫ p, Real.exp ((a / Real.sqrt (∑ i, (k i : ℝ))) *
        ∑ b, (perronMass M hM b)⁻¹ * (pooledSum M hM k (coordinateTest b) p) ^ 2)
          ∂productLaw M k r g hC) - 1 ∧
        (∫ p, Real.exp ((a / Real.sqrt (∑ i, (k i : ℝ))) *
          ∑ b, (perronMass M hM b)⁻¹ * (pooledSum M hM k (coordinateTest b) p) ^ 2)
            ∂productLaw M k r g hC) - 1 ≤ D / Real.sqrt (∑ i, (k i : ℝ)) := by
  let B : ℝ := 1 + ∑ b, (perronMass M hM b)⁻¹
  have hB : 0 < B := by
    have hp : 0 ≤ ∑ b, (perronMass M hM b)⁻¹ :=
      Finset.sum_nonneg (fun b _ ↦ (inv_pos.mpr (perronMass_pos M hM b)).le)
    dsimp only [B]
    linarith
  obtain ⟨D, hD, hb⟩ := exists_uniform_pooled_square_moment_bound M hM R q hq L (A * B)
    hL (mul_nonneg hA hB.le)
  refine ⟨D, hD, ?_⟩
  intro k r hk hr g hg a ha haA hC
  have hs := Real.sqrt_pos.mpr (totalSize_pos hq k hk)
  apply ProfileSquareSeries.integral_exp_finset_squares_sub_one_le
    (productLaw M k r g hC) Finset.univ
    (fun b ↦ (perronMass M hM b)⁻¹)
    (fun b p ↦ pooledSum M hM k (coordinateTest b) p) ha hB hs (by positivity)
  · intro b _
    exact (inv_pos.mpr (perronMass_pos M hM b)).le
  · dsimp only [B]
    linarith
  · intro b _
    exact pooledSum_measurable M hM k (coordinateTest b)
  · intro b _ p
    have hp := pooledSum_abs_le M hM hq k hk (coordinateTest b) p
    have hm := mul_le_mul_of_nonneg_left (norm_coordinateTest_le b)
      (by positivity : 0 ≤ 2 * Real.sqrt (∑ i, (k i : ℝ)))
    exact hp.trans (by simpa only [mul_one] using hm)
  · intro b _
    exact (hb k r hk hr g hg (coordinateTest b) (norm_coordinateTest_le b)
      (a * B) (mul_nonneg ha hB.le) (mul_le_mul_of_nonneg_right haA hB.le) hC).2

/-- Pearson exponential moments at the paper's A/n scale tend to one.
This is proved from actual q-product field moments, not assumed UI. -/
theorem pearson_exponential_tendsto_one (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q) (L A C₀ : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hC₀ : 0 ≤ C₀)
    (k r : ℕ → Fin q → ℕ) (g : ℕ → Fin q → C(S, ℝ))
    (hk : ∀ n i, 0 < k n i)
    (hC : ∀ n i, 0 < M.bjrModel.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hKt : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C₀ * (n + 1 : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun n ↦ ∫ p, Real.exp ((A / (n + 1 : ℝ)) * pearson M hM (k n) p)
      ∂productLaw M (k n) (r n) (g n) (hC n)) atTop (𝓝 1) := by
  obtain ⟨D, _hD, hb⟩ := exists_uniform_pearson_square_bound M hM R q hq L
    (A * C₀ ^ (3 / 2 : ℝ)) hL (mul_nonneg hA (Real.rpow_nonneg hC₀ _))
  have hbound : ∀ᶠ n in atTop,
      0 ≤ (∫ p, Real.exp ((A / (n + 1 : ℝ)) * pearson M hM (k n) p)
        ∂productLaw M (k n) (r n) (g n) (hC n)) - 1 ∧
      (∫ p, Real.exp ((A / (n + 1 : ℝ)) * pearson M hM (k n) p)
        ∂productLaw M (k n) (r n) (g n) (hC n)) - 1 ≤
          D / Real.sqrt (∑ i, (k n i : ℝ)) := by
    filter_upwards [hr, hg, hsize] with n hnr hng hns
    have hK := totalSize_pos hq (k n) (hk n)
    have hs := Real.sqrt_pos.mpr hK
    let a : ℝ := A * (∑ i, (k n i : ℝ)) / (n + 1 : ℝ) * Real.sqrt (∑ i, (k n i : ℝ))
    have ha : 0 ≤ a := by dsimp only [a]; positivity
    have har : a ≤ A * C₀ ^ (3 / 2 : ℝ) := by
      have hc := (ProfileScaleMatched.coefficient_bounds hK (by positivity : (0 : ℝ) < n + 1)
        hC₀ hA hns).2
      exact (le_div_iff₀ hs).mp hc
    have he := hb (k n) (r n) (hk n) hnr (g n) hng a ha har (hC n)
    have heq (p : StateFamily (S := S) (k n)) :
        (A / (n + 1 : ℝ)) * pearson M hM (k n) p =
        (a / Real.sqrt (∑ i, (k n i : ℝ))) *
          ∑ b, (perronMass M hM b)⁻¹ * (pooledSum M hM (k n) (coordinateTest b) p) ^ 2 := by
      rw [pearson_eq_coordinate_squares M hM hq (k n) (hk n) p]
      dsimp only [a]
      field_simp [hs.ne']
    simpa only [← heq] using he
  have hz : Tendsto (fun n ↦ D / Real.sqrt (∑ i, (k n i : ℝ))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hKt)).const_mul D
  have hsub : Tendsto (fun n ↦ (∫ p, Real.exp ((A / (n + 1 : ℝ)) * pearson M hM (k n) p)
      ∂productLaw M (k n) (r n) (g n) (hC n)) - 1) atTop (𝓝 0) :=
    squeeze_zero' (hbound.mono (fun _ h ↦ h.1)) (hbound.mono (fun _ h ↦ h.2)) hz
  simpa only [sub_add_cancel, zero_add] using hsub.add_const 1

/-- Model-only Pearson terminal. The actual product laws are defined by
normalizers proved positive from finite field enumeration. Only literal
size, surplus, and critical-field window conditions remain as inputs. -/
theorem exists_actual_pearson_exponential_tendsto_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R q : ℕ) (hq : 0 < q) (L A C₀ : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hC₀ : 0 ≤ C₀) :
    ∃ K₀ : ℕ, ∃ _hK₀ : 0 < K₀,
      ∃ pos : ∀ k : ℕ, K₀ ≤ k → ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        0 < M.bjrModel.fieldConnectedWeight g k r,
      ∀ k r : ℕ → Fin q → ℕ, ∀ hk : ∀ n i, K₀ ≤ k n i,
      ∀ hr : ∀ n i, r n i ≤ R, ∀ g : ℕ → Fin q → C(S, ℝ),
      Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop →
      (∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L) →
      (∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C₀ * (n + 1 : ℝ) ^ (2 / 3 : ℝ)) →
      Tendsto (fun n ↦ ∫ p, Real.exp ((A / (n + 1 : ℝ)) * pearson M hM (k n) p)
        ∂productLaw M (k n) (r n) (g n)
          (fun i ↦ pos (k n i) (hk n i) (r n i) (hr n i) (g n i))) atTop (𝓝 1) := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (eventually_all_field_normalizers_pos M hM R)
  let K₀ := max K 1
  have hK₀ : 0 < K₀ := by dsimp only [K₀]; omega
  have pos : ∀ k : ℕ, K₀ ≤ k → ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
      0 < M.bjrModel.fieldConnectedWeight g k r :=
    fun k hk r hr g ↦ hK k (by dsimp only [K₀] at hk; omega) r hr g
  refine ⟨K₀, hK₀, pos, ?_⟩
  intro k r hk hr g hKt hg hsize
  exact pearson_exponential_tendsto_one M hM R q hq L A C₀ hL hA hC₀ k r g
    (fun n i ↦ hK₀.trans_le (hk n i))
    (fun n i ↦ pos (k n i) (hk n i) (r n i) (hr n i) (g n i)) hKt
    (Eventually.of_forall hr) hg hsize

end PerronWright.FiniteIrreduciblePearsonProfile
