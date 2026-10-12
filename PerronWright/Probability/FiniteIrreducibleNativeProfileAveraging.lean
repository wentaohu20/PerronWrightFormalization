import PerronWright.Probability.FiniteIrreducibleDepletionAveraging
import PerronWright.Probability.FiniteIrreducibleDeterministicConnectedLawFormula
import PerronWright.Probability.CriticalScalarField

/-! # Native finite connected-product profile averages at the actual critical time

The literal pooled type fibres in the exact deterministic component
formula coincide with the integer coordinate counts used in the proved
Pearson moments. Critical scalar fields satisfy the profile-field domain
by the actual time/size estimates, with no regular/B2 adapter.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FiniteIrreducibleNativeProfileAveraging

open FiniteIrreduciblePearsonProfile FiniteIrreducibleProfileFiniteCollection
open FiniteIrreducibleDepletionAveraging FiniteIrreducibleDeterministicDepletion
open FiniteIrreducibleConnectedLawFiniteSum FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)
open FiniteIrreducibleProfileLaplace (eventually_all_field_normalizers_pos)

theorem aggregateCount_eq_pooledFiberCount {S : Type*} [Fintype S] [DecidableEq S]
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) (a : S) :
    aggregateCount k p a = fiberCount (pooledTypes p) a := by
  unfold fiberCount
  rw [Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_sigma]
  simp only [aggregateCount, pooledTypes, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem aggregateCount_eq_pooledFiberCounts {S : Type*} [Fintype S] [DecidableEq S]
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) :
    aggregateCount k p = fiberCount (pooledTypes p) :=
  funext (aggregateCount_eq_pooledFiberCount k p)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem productLaw_constant_eq_native (M : FiniteIrreducibleModel S)
    (g : C(S, ℝ)) {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight g (k i) (r i)) :
    productLaw M k r (fun _ ↦ g) hC = connectedProductLaw M g k r hC := rfl

/-- The literal scalar field is genuinely admissible uniformly over all
critical-size components, including at the native unshifted n scale. -/
theorem exists_native_scalarField_bound (M : FiniteIrreducibleModel S)
    (lambda C : ℝ) (hC : 0 ≤ C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
      Real.sqrt (k : ℝ) * ‖M.bjrModel.scalarField (CriticalScaling.time lambda n)‖ ≤ L := by
  let N : ℕ → ℕ := fun n ↦ max n 1
  have hN : ∀ n, 0 < N n := fun n ↦ by dsimp only [N]; omega
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_max_left n 1) tendsto_id
  obtain ⟨L, hL, hb⟩ := CriticalScalarField.exists_sqrt_scalarField_bound
    M.bjrModel N hN hNt lambda C hC
  refine ⟨L, hL, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have heq : N n = n := max_eq_left hn1
  simpa only [heq] using hn

theorem pearson_native_exponential_tendsto_one (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q) (lambda A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (k r : ℕ → Fin q → ℕ)
    (hk : ∀ n i, 0 < k n i)
    (pos : ∀ n i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n i) (r n i))
    (hKt : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun n ↦ ∫ p, Real.exp ((A / (n : ℝ)) * pearson M hM (k n) p)
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
        (k n) (r n) (pos n)) atTop (𝓝 1) := by
  obtain ⟨L, hL, hfield⟩ := exists_native_scalarField_bound M lambda C hC
  have hg : ∀ᶠ n in atTop, ∀ i,
      Real.sqrt (k n i : ℝ) * ‖M.bjrModel.scalarField (CriticalScaling.time lambda n)‖ ≤ L := by
    filter_upwards [hfield, hsize] with n hn hsn
    intro i
    exact hn (k n i) ((Finset.single_le_sum
      (fun j _ ↦ Nat.cast_nonneg (k n j)) (Finset.mem_univ i)).trans hsn)
  have hs' : ∀ᶠ n in atTop,
      (∑ i, (k n i : ℝ)) ≤ C * (n + 1 : ℝ) ^ (2 / 3 : ℝ) := by
    filter_upwards [hsize] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith : (n : ℝ) ≤ n + 1)
        (by norm_num : (0 : ℝ) ≤ 2 / 3)) hC)
  have hupper := pearson_exponential_tendsto_one M hM R q hq L (2 * A) C hL
    (mul_nonneg (by norm_num) hA) hC k r
      (fun n _ ↦ M.bjrModel.scalarField (CriticalScaling.time lambda n)) hk pos hKt hr hg hs'
  simp only [productLaw_constant_eq_native] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun n ↦ by
      have hh := integral_mono (μ := connectedProductLaw M
        (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n) (r n) (pos n))
        (f := fun _ ↦ (1 : ℝ)) (g := fun p ↦ Real.exp ((A / (n : ℝ)) * pearson M hM (k n) p))
        (integrable_const 1) Integrable.of_finite
        (fun p ↦ Real.one_le_exp (mul_nonneg (div_nonneg hA (Nat.cast_nonneg n))
          (pearson_nonneg M hM (k n) p)))
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hb : A / (n : ℝ) ≤ (2 * A) / (n + 1 : ℝ) := by
      apply (div_le_div_iff₀ hnR (by positivity)).mpr
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro p
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb (pearson_nonneg M hM (k n) p))

/-- Native model-only terminal at the literal A/n scale and the literal
critical graph time. The field-size condition and all positive
normalizers are proved, not supplied as profile inputs. -/
theorem exists_actual_native_pearson_exponential_limit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q)
    (lambda A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ K₀ : ℕ, ∃ _hK₀ : 0 < K₀,
      ∃ pos : ∀ k : ℕ, K₀ ≤ k → ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        0 < M.bjrModel.fieldConnectedWeight g k r,
      ∀ k r : ℕ → Fin q → ℕ, ∀ hk : ∀ n i, K₀ ≤ k n i,
      ∀ hr : ∀ n i, r n i ≤ R,
      Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop →
      (∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) →
      Tendsto (fun n ↦ ∫ p, Real.exp ((A / (n : ℝ)) * pearson M hM (k n) p)
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
          (k n) (r n) (fun i ↦ pos (k n i) (hk n i) (r n i) (hr n i)
            (M.bjrModel.scalarField (CriticalScaling.time lambda n)))) atTop (𝓝 1) := by
  obtain ⟨K₀, hK₀, pos, _⟩ := exists_actual_target_population_L1_limit M hM R q
  refine ⟨K₀, hK₀, pos, ?_⟩
  intro k r hk hr hKt hsize
  exact pearson_native_exponential_tendsto_one M hM R q hq lambda A C hA hC k r
    (fun n i ↦ hK₀.trans_le (hk n i)) _ hKt (Eventually.of_forall hr) hsize

/-- Actual L1 control of every Pearson-dominated exponent under the
native laws. This derives exponential averaging, not an assumed UI step. -/
theorem native_pearson_dominated_exponential_L1_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q) (lambda A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (k r : ℕ → Fin q → ℕ)
    (hk : ∀ n i, 0 < k n i)
    (pos : ∀ n i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n i) (r n i))
    (hKt : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ))
    (Q : ∀ n, StateFamily (S := S) (k n) → ℝ)
    (hdom : ∀ᶠ n in atTop, ∀ p, |Q n p| ≤ (A / (n : ℝ)) * pearson M hM (k n) p) :
    Tendsto (fun n ↦ ∫ p, |Real.exp (Q n p) - 1|
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
        (k n) (r n) (pos n)) atTop (𝓝 0) := by
  have hz := (pearson_native_exponential_tendsto_one M hM R q hq lambda A C
    hA hC k r hk pos hKt hr hsize).sub_const 1
  simp only [sub_self] at hz
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ integral_nonneg (fun _ ↦ abs_nonneg _)))
    _ hz
  filter_upwards [hdom] with n hn
  have hh := integral_mono (μ := connectedProductLaw M
    (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n) (r n) (pos n))
    (f := fun p ↦ |Real.exp (Q n p) - 1|)
    (g := fun p ↦ Real.exp ((A / (n : ℝ)) * pearson M hM (k n) p) - 1)
    Integrable.of_finite Integrable.of_finite (fun p ↦
      (BoundedConcentrationTransfer.abs_exp_sub_one_le_exp_abs_sub_one _).trans
        (sub_le_sub_right (Real.exp_le_exp.mpr (hn p)) 1))
  rw [integral_sub Integrable.of_finite (integrable_const 1), integral_const] at hh
  simpa only [probReal_univ, smul_eq_mul, one_mul] using hh

/-- Literal pooled fibre-count weights under the native critical-time
connected-product law. Arbitrary deterministic O(1) counts are handled;
the law cutoff is proved from the actual finite model. -/
theorem exists_actual_native_population_L1_limit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (lambda : ℝ) :
    ∃ K₀ : ℕ, ∃ _hK₀ : 0 < K₀,
      ∃ pos : ∀ k : ℕ, K₀ ≤ k → ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        0 < M.bjrModel.fieldConnectedWeight g k r,
      ∀ k r : ℕ → Fin q → ℕ, ∀ hk : ∀ n i, K₀ ≤ k n i,
      ∀ hr : ∀ n i, r n i ≤ R, ∀ c : ℕ → S → ℕ, ∀ D C : ℝ,
      0 ≤ D → 0 ≤ C →
      (∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) →
      (∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) →
      Tendsto (fun n ↦ ∫ p,
        |targetLeadingCorrection M n (c n) (fiberCount (pooledTypes p)) *
          populationCorrection M n (c n) (fiberCount (pooledTypes p))
            (CriticalScaling.time lambda n) - 1|
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
          (k n) (r n) (fun i ↦ pos (k n i) (hk n i) (r n i) (hr n i)
            (M.bjrModel.scalarField (CriticalScaling.time lambda n)))) atTop (𝓝 0) := by
  obtain ⟨K₀, hK₀, pos, hlimit⟩ := exists_actual_target_population_L1_limit M hM R q
  refine ⟨K₀, hK₀, pos, ?_⟩
  intro k r hk hr c D C hD hC hround hsize
  have ht : ∀ᶠ n in atTop, |CriticalScaling.time lambda n| ≤ 2 := by
    have hh := (CriticalScaling.time_tendsto lambda).abs
    simp only [abs_one] at hh
    exact (hh.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))).mono (fun _ h ↦ h.le)
  have hl := hlimit k r hk hr
    (fun n _ ↦ M.bjrModel.scalarField (CriticalScaling.time lambda n)) c
    (CriticalScaling.time lambda) D 2 C hD (by norm_num) hC hround ht hsize
  simpa only [aggregateCount_eq_pooledFiberCounts, productLaw_constant_eq_native] using hl

/-- The proved Pearson moment absorbs a genuinely vanishing deterministic
remainder as well, on the changing actual component-state spaces. -/
theorem native_pearson_with_remainder_exponential_L1_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q) (lambda A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (k r : ℕ → Fin q → ℕ)
    (hk : ∀ n i, 0 < k n i)
    (pos : ∀ n i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n i) (r n i))
    (hKt : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ))
    (Q : ∀ n, StateFamily (S := S) (k n) → ℝ) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (𝓝 0))
    (hdom : ∀ᶠ n in atTop, ∀ p, |Q n p| ≤ (A / (n : ℝ)) * pearson M hM (k n) p + err n) :
    Tendsto (fun n ↦ ∫ p, |Real.exp (Q n p) - 1|
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
        (k n) (r n) (pos n)) atTop (𝓝 0) := by
  have hm := pearson_native_exponential_tendsto_one M hM R q hq lambda A C hA hC k r hk pos hKt hr hsize
  have he : Tendsto (fun n ↦ Real.exp |err n|) atTop (𝓝 1) := by
    simpa only [Function.comp_def, abs_zero, Real.exp_zero] using
      Real.continuous_exp.tendsto (|(0 : ℝ)|) |>.comp herr.abs
  have hz := (hm.mul he).sub_const 1
  simp only [mul_one, sub_self] at hz
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ integral_nonneg (fun _ ↦ abs_nonneg _)))
    _ hz
  filter_upwards [hdom] with n hn
  have hh := integral_mono (μ := connectedProductLaw M
    (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n) (r n) (pos n))
    (f := fun p ↦ |Real.exp (Q n p) - 1|)
    (g := fun p ↦ Real.exp ((A / (n : ℝ)) * pearson M hM (k n) p) * Real.exp |err n| - 1)
    Integrable.of_finite Integrable.of_finite (fun p ↦ by
      dsimp only
      rw [← Real.exp_add]
      exact (BoundedConcentrationTransfer.abs_exp_sub_one_le_exp_abs_sub_one _).trans
        (sub_le_sub_right (Real.exp_le_exp.mpr ((hn p).trans
          (add_le_add le_rfl (le_abs_self _)))) 1))
  rw [integral_sub Integrable.of_finite (integrable_const 1), integral_mul_const, integral_const] at hh
  simpa only [probReal_univ, smul_eq_mul, one_mul] using hh

end PerronWright.FiniteIrreducibleNativeProfileAveraging
