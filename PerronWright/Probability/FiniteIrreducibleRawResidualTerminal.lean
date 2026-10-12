import PerronWright.Probability.FiniteIrreducibleRawResidualAveraging

/-! # Model-only deterministic finite residual terminal

All connected-law normalizers are obtained from the proved finite
irreducible field enumeration. The normalized literal raw residual has
true L1 and mean limits for arbitrary O(1)-rounded type counts. In
particular no residual-average, profile, or UI interface is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleRawResidualTerminal

open FiniteIrreducibleRawResidualAveraging FiniteIrreducibleResidualNormalization
open FiniteIrreducibleNativeProfileAveraging FiniteIrreduciblePerronCountExpansion
open FiniteIrreducibleProfileFiniteCollection
open FiniteIrreducibleDeterministicResidualWeights (residual)
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)

/-- Literal changing-space L1 convergence implies a genuine mean limit. -/
theorem mean_tendsto_one_of_L1
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, Finite (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ)
    (hL : Tendsto (fun n ↦ ∫ p, |X n p - 1| ∂μ n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ p, X n p ∂μ n) atTop (𝓝 1) := by
  have habs : Tendsto (fun n ↦ |(∫ p, X n p ∂μ n) - 1|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ abs_nonneg _)) _ hL
    exact Eventually.of_forall (fun n ↦ by
      have h := abs_integral_le_integral_abs (μ := μ n) (f := fun p ↦ X n p - 1)
      rw [integral_sub Integrable.of_finite (integrable_const 1), integral_const] at h
      simpa only [probReal_univ, smul_eq_mul, one_mul] using h)
  simpa only [Real.norm_eq_abs] using (tendsto_iff_norm_sub_tendsto_zero.mpr habs)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem integral_normalizedResidual (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (n : ℕ) (c : S → ℕ) {q : ℕ} (k r : Fin q → ℕ)
    (pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i)) :
    (∫ p, normalizedResidual M hM lambda n c p
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) =
      (∫ p, residual M (CriticalScaling.time lambda n) n c p
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) /
      Real.exp (mainExponent M hM (n : ℝ) (∑ i, (k i : ℝ)) (CriticalScaling.time lambda n)) := by
  unfold normalizedResidual
  rw [integral_mul_const, Real.exp_neg]
  rfl

/-- Actual finite critical model terminal for the full graph residual.
The literal type law may be periodic: no B2/primitive assumption occurs. -/
theorem exists_actual_native_rawResidual_L1_and_mean_limits
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q)
    (lambda : ℝ) :
    ∃ K₀ : ℕ, ∃ _hK₀ : 0 < K₀,
      ∃ pos : ∀ k : ℕ, K₀ ≤ k → ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        0 < M.bjrModel.fieldConnectedWeight g k r,
      ∀ k r : ℕ → Fin q → ℕ, ∀ hk : ∀ n i, K₀ ≤ k n i,
      ∀ hr : ∀ n i, r n i ≤ R,
      ∀ c : ℕ → S → ℕ, ∀ D C : ℝ, 0 ≤ D → 0 ≤ C →
      (∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) →
      Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop →
      (∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) →
      let μ := fun n ↦ connectedProductLaw M
        (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n) (r n)
        (fun i ↦ pos (k n i) (hk n i) (r n i) (hr n i)
          (M.bjrModel.scalarField (CriticalScaling.time lambda n)))
      Tendsto (fun n ↦ ∫ p, |normalizedResidual M hM lambda n (c n) p - 1| ∂μ n)
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ (∫ p, residual M (CriticalScaling.time lambda n) n (c n) p ∂μ n) /
        Real.exp (mainExponent M hM (n : ℝ) (∑ i, (k n i : ℝ)) (CriticalScaling.time lambda n)))
        atTop (𝓝 1) := by
  obtain ⟨K₀, hK₀, pos, _⟩ := exists_actual_native_population_L1_limit M hM R q lambda
  refine ⟨K₀, hK₀, pos, ?_⟩
  intro k r hk hr c D C hD hC hround hKt hsize
  dsimp only
  let μ := fun n ↦ connectedProductLaw M
    (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n) (r n)
    (fun i ↦ pos (k n i) (hk n i) (r n i) (hr n i)
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)))
  have hL := native_normalizedResidual_L1_tendsto_zero M hM R q hq lambda c D C hD hC hround
    k r (fun n i ↦ hK₀.trans_le (hk n i))
      (fun n i ↦ pos (k n i) (hk n i) (r n i) (hr n i)
        (M.bjrModel.scalarField (CriticalScaling.time lambda n))) hKt (Eventually.of_forall hr) hsize
  refine ⟨hL, ?_⟩
  have hh := mean_tendsto_one_of_L1 μ (fun n ↦ normalizedResidual M hM lambda n (c n)) hL
  simpa only [μ, integral_normalizedResidual] using hh

end PerronWright.FiniteIrreducibleRawResidualTerminal
