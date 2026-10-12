import PerronWright.Probability.FiniteIrreducibleDeterministicDepletion
import PerronWright.Probability.FiniteIrreduciblePearsonProfile
import PerronWright.Probability.FiniteIrreducibleDepletionRounding
import PerronWright.Probability.BoundedConcentrationTransfer

/-! # Actual finite-population correction averages

The literal descending factorial and population correction are averaged
under genuine independent connected-state laws. Uniform deterministic
errors control the entire state space, including its atypical profiles.
Positive normalizers in the model terminal are derived from enumeration.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FiniteIrreducibleDepletionAveraging

open FiniteIrreducibleDeterministicDepletion FiniteIrreduciblePearsonProfile
open FiniteIrreducibleDepletionRounding
open FiniteIrreducibleProfileFiniteCollection
open FiniteIrreducibleProfileLaplace (eventually_all_field_normalizers_pos)

/-- Uniform convergence, on changing finite probability spaces, really
implies convergence of the literal absolute-error integrals. -/
theorem integral_abs_tendsto_zero_of_uniform
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, Finite (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (err : ℕ → ℝ) (ht : Tendsto err atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ ω, |X n ω| ≤ err n) :
    Tendsto (fun n ↦ ∫ ω, |X n ω| ∂μ n) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ integral_nonneg (fun _ ↦ abs_nonneg _)))
    _ ht
  filter_upwards [hbound] with n hn
  have hi := integral_mono (μ := μ n) (f := fun ω ↦ |X n ω|)
    (g := fun _ ↦ err n) Integrable.of_finite (integrable_const _) hn
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Actual multiplicative correction of literal depletion by its proved
quadratic/cubic ambient-count exponent. -/
def normalizedLeadingCorrection (c K : S → ℕ) : ℝ :=
  normalizedDepletion c K * Real.exp
    ((∑ a, (K a : ℝ) ^ 2 / (2 * c a)) +
      ∑ a, (K a : ℝ) ^ 3 / (6 * (c a : ℝ) ^ 2))

omit [DecidableEq S] [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem normalizedLeadingCorrection_eq_exp (c K : S → ℕ)
    (hpos : 0 < normalizedDepletion c K) :
    normalizedLeadingCorrection c K = Real.exp
      (Real.log (normalizedDepletion c K) +
        (∑ a, (K a : ℝ) ^ 2 / (2 * c a)) +
          ∑ a, (K a : ℝ) ^ 3 / (6 * (c a : ℝ) ^ 2)) := by
  simp only [normalizedLeadingCorrection, Real.exp_add, Real.exp_log hpos]
  ring

theorem populationCorrection_L1_tendsto_zero (M : FiniteIrreducibleModel S)
    {q : ℕ} (k : ℕ → Fin q → ℕ)
    (μ : ∀ n, Measure (StateFamily (S := S) (k n))) [∀ n, IsProbabilityMeasure (μ n)]
    (c : ℕ → S → ℕ) (t : ℕ → ℝ) (D T C : ℝ)
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (ht : ∀ᶠ n in atTop, |t n| ≤ T)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun n ↦ ∫ p,
      |populationCorrection M n (c n) (aggregateCount (k n) p) (t n) - 1| ∂μ n)
        atTop (𝓝 0) := by
  let err : ℕ → ℝ := fun n ↦ populationBudget M D T * C * (n : ℝ) ^ (-(1 / 3 : ℝ))
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop).const_mul (populationBudget M D T * C)
  have he : Tendsto (fun n ↦ Real.exp |err n| - 1) atTop (𝓝 0) := by
    simpa using (Real.continuous_exp.tendsto (|(0 : ℝ)|) |>.comp herr.abs).sub_const 1
  apply integral_abs_tendsto_zero_of_uniform μ
    (fun n p ↦ populationCorrection M n (c n) (aggregateCount (k n) p) (t n) - 1)
    (fun n ↦ Real.exp |err n| - 1) he
  filter_upwards [populationCorrection_uniform_log_bound M c D T C hD hT hC hround,
    ht, hsize] with n hn htn hsn
  intro p
  have hh := hn (aggregateCount (k n) p) (t n)
    (by simpa only [sum_aggregateCount_real] using hsn) htn
  rw [← Real.exp_log hh.1]
  exact (BoundedConcentrationTransfer.abs_exp_sub_one_le_exp_abs_sub_one _).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (hh.2.trans (le_abs_self (err n)))) 1)

theorem normalizedLeadingCorrection_L1_tendsto_zero (M : FiniteIrreducibleModel S)
    {q : ℕ} (k : ℕ → Fin q → ℕ)
    (μ : ∀ n, Measure (StateFamily (S := S) (k n))) [∀ n, IsProbabilityMeasure (μ n)]
    (c : ℕ → S → ℕ) (D C : ℝ) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun n ↦ ∫ p,
      |normalizedLeadingCorrection (c n) (aggregateCount (k n) p) - 1| ∂μ n)
        atTop (𝓝 0) := by
  obtain ⟨err, herr, hbound⟩ := normalizedDepletion_uniform_leading_remainder M c D C hC hround
  have he : Tendsto (fun n ↦ Real.exp |err n| - 1) atTop (𝓝 0) := by
    simpa using (Real.continuous_exp.tendsto (|(0 : ℝ)|) |>.comp herr.abs).sub_const 1
  apply integral_abs_tendsto_zero_of_uniform μ
    (fun n p ↦ normalizedLeadingCorrection (c n) (aggregateCount (k n) p) - 1)
    (fun n ↦ Real.exp |err n| - 1) he
  filter_upwards [hbound, hsize] with n hn hsn
  intro p
  have hh := hn (aggregateCount (k n) p) (by simpa only [sum_aggregateCount_real] using hsn)
  rw [normalizedLeadingCorrection_eq_exp _ _ hh.1]
  exact (BoundedConcentrationTransfer.abs_exp_sub_one_le_exp_abs_sub_one _).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (hh.2.trans (le_abs_self (err n)))) 1)

/-- True connected-law averages, with positivity obtained solely from
the literal finite irreducible critical model and its field enumeration.
Arbitrary deterministic O(1)-rounded counts are allowed. -/
theorem exists_actual_finite_population_L1_limits
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) :
    ∃ K₀ : ℕ, ∃ _hK₀ : 0 < K₀,
      ∃ pos : ∀ k : ℕ, K₀ ≤ k → ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        0 < M.bjrModel.fieldConnectedWeight g k r,
      ∀ k r : ℕ → Fin q → ℕ, ∀ hk : ∀ n i, K₀ ≤ k n i,
      ∀ hr : ∀ n i, r n i ≤ R, ∀ g : ℕ → Fin q → C(S, ℝ),
      ∀ c : ℕ → S → ℕ, ∀ t : ℕ → ℝ, ∀ D T C : ℝ,
      0 ≤ D → 0 ≤ T → 0 ≤ C →
      (∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) →
      (∀ᶠ n in atTop, |t n| ≤ T) →
      (∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) →
      let μ := fun n ↦ productLaw M (k n) (r n) (g n)
        (fun i ↦ pos (k n i) (hk n i) (r n i) (hr n i) (g n i))
      Tendsto (fun n ↦ ∫ p,
        |populationCorrection M n (c n) (aggregateCount (k n) p) (t n) - 1| ∂μ n)
          atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ p,
        |normalizedLeadingCorrection (c n) (aggregateCount (k n) p) - 1| ∂μ n)
          atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (eventually_all_field_normalizers_pos M hM R)
  let K₀ := max K 1
  have hK₀ : 0 < K₀ := by dsimp only [K₀]; omega
  have pos : ∀ k : ℕ, K₀ ≤ k → ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
      0 < M.bjrModel.fieldConnectedWeight g k r :=
    fun k hk r hr g ↦ hK k (by dsimp only [K₀] at hk; omega) r hr g
  refine ⟨K₀, hK₀, pos, ?_⟩
  intro k r hk hr g c t D T C hD hT hC hround ht hsize
  exact ⟨populationCorrection_L1_tendsto_zero M k _ c t D T C hD hT hC hround ht hsize,
    normalizedLeadingCorrection_L1_tendsto_zero M k _ c D C hC hround hsize⟩

/-- The literal selection correction in the fixed target coordinates. -/
def targetLeadingCorrection (M : FiniteIrreducibleModel S) (n : ℕ) (c K : S → ℕ) : ℝ :=
  normalizedDepletion c K * Real.exp
    ((∑ a, (K a : ℝ) ^ 2 / (2 * (n : ℝ) * M.weight a)) +
      ∑ a, (K a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2))

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem targetLeadingCorrection_eq_exp (M : FiniteIrreducibleModel S)
    (n : ℕ) (c K : S → ℕ) (hpos : 0 < normalizedDepletion c K) :
    targetLeadingCorrection M n c K = Real.exp
      (Real.log (normalizedDepletion c K) +
        (∑ a, (K a : ℝ) ^ 2 / (2 * (n : ℝ) * M.weight a)) +
          ∑ a, (K a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2)) := by
  simp only [targetLeadingCorrection, Real.exp_add, Real.exp_log hpos]
  ring

/-- Actual finite-population weight averaging after the fixed-μ leading
exponent is removed. Both selection and ν−μ population corrections are
included, and the whole state space is controlled by a uniform bound. -/
theorem target_population_correction_L1_tendsto_zero (M : FiniteIrreducibleModel S)
    {q : ℕ} (k : ℕ → Fin q → ℕ)
    (μ : ∀ n, Measure (StateFamily (S := S) (k n))) [∀ n, IsProbabilityMeasure (μ n)]
    (c : ℕ → S → ℕ) (t : ℕ → ℝ) (D T C : ℝ)
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (ht : ∀ᶠ n in atTop, |t n| ≤ T)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun n ↦ ∫ p,
      |targetLeadingCorrection M n (c n) (aggregateCount (k n) p) *
        populationCorrection M n (c n) (aggregateCount (k n) p) (t n) - 1| ∂μ n)
          atTop (𝓝 0) := by
  obtain ⟨err, herr, hbound⟩ := normalizedDepletion_uniform_target_remainder M c D C hD hC hround
  let popErr : ℕ → ℝ := fun n ↦ populationBudget M D T * C * (n : ℝ) ^ (-(1 / 3 : ℝ))
  have hpop : Tendsto popErr atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop).const_mul (populationBudget M D T * C)
  have hz : Tendsto (fun n ↦ err n + popErr n) atTop (𝓝 0) := by
    simpa only [zero_add] using herr.add hpop
  have he : Tendsto (fun n ↦ Real.exp |err n + popErr n| - 1) atTop (𝓝 0) := by
    simpa using (Real.continuous_exp.tendsto (|(0 : ℝ)|) |>.comp hz.abs).sub_const 1
  apply integral_abs_tendsto_zero_of_uniform μ
    (fun n p ↦ targetLeadingCorrection M n (c n) (aggregateCount (k n) p) *
      populationCorrection M n (c n) (aggregateCount (k n) p) (t n) - 1)
    (fun n ↦ Real.exp |err n + popErr n| - 1) he
  filter_upwards [hbound, populationCorrection_uniform_log_bound M c D T C hD hT hC hround,
    hsize, ht] with n hn hpn hsn htn
  intro p
  have hs : (∑ a, (aggregateCount (k n) p a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) := by
    simpa only [sum_aggregateCount_real] using hsn
  have hd := hn (aggregateCount (k n) p) hs
  have hp := hpn (aggregateCount (k n) p) (t n) hs htn
  rw [targetLeadingCorrection_eq_exp _ _ _ _ hd.1,
    ← Real.exp_log hp.1, ← Real.exp_add]
  have hb : |Real.log (normalizedDepletion (c n) (aggregateCount (k n) p)) +
      (∑ a, (aggregateCount (k n) p a : ℝ) ^ 2 / (2 * (n : ℝ) * M.weight a)) +
      (∑ a, (aggregateCount (k n) p a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2)) +
      Real.log (populationCorrection M n (c n) (aggregateCount (k n) p) (t n))| ≤
        |err n + popErr n| :=
    (abs_add_le _ _).trans ((add_le_add hd.2 hp.2).trans (le_abs_self _))
  exact (BoundedConcentrationTransfer.abs_exp_sub_one_le_exp_abs_sub_one _).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hb) 1)

/-- The finite model itself supplies all law normalizers for the actual
fixed-target population correction average. No profile/UI premise occurs. -/
theorem exists_actual_target_population_L1_limit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) :
    ∃ K₀ : ℕ, ∃ _hK₀ : 0 < K₀,
      ∃ pos : ∀ k : ℕ, K₀ ≤ k → ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        0 < M.bjrModel.fieldConnectedWeight g k r,
      ∀ k r : ℕ → Fin q → ℕ, ∀ hk : ∀ n i, K₀ ≤ k n i,
      ∀ hr : ∀ n i, r n i ≤ R, ∀ g : ℕ → Fin q → C(S, ℝ),
      ∀ c : ℕ → S → ℕ, ∀ t : ℕ → ℝ, ∀ D T C : ℝ,
      0 ≤ D → 0 ≤ T → 0 ≤ C →
      (∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) →
      (∀ᶠ n in atTop, |t n| ≤ T) →
      (∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) →
      Tendsto (fun n ↦ ∫ p,
        |targetLeadingCorrection M n (c n) (aggregateCount (k n) p) *
          populationCorrection M n (c n) (aggregateCount (k n) p) (t n) - 1|
        ∂productLaw M (k n) (r n) (g n)
          (fun i ↦ pos (k n i) (hk n i) (r n i) (hr n i) (g n i))) atTop (𝓝 0) := by
  obtain ⟨K₀, hK₀, pos, _⟩ := exists_actual_finite_population_L1_limits M hM R q
  refine ⟨K₀, hK₀, pos, ?_⟩
  intro k r hk hr g c t D T C hD hT hC hround ht hsize
  exact target_population_correction_L1_tendsto_zero M k _ c t D T C
    hD hT hC hround ht hsize

end PerronWright.FiniteIrreducibleDepletionAveraging
