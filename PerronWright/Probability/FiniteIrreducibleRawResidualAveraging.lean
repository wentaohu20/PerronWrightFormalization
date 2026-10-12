import PerronWright.Probability.FiniteIrreducibleResidualNormalization

/-! # Actual deterministic raw residual averages

The native connected-product law comes from the true finite model. The
full raw residual is normalized by its literal Perron size exponent.
The actual Pearson exponential estimate absorbs the isolation error;
all other logarithmic errors tend uniformly to zero, with the odds
estimate used only almost everywhere on the genuine connected support.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleRawResidualAveraging

open FiniteIrreducibleResidualNormalization FiniteIrreducibleNativeProfileAveraging
open FiniteIrreducibleIsolationBounds FiniteIrreducibleIsolationAveraging
open FiniteIrreducibleDeterministicDepletion FiniteIrreducibleDepletionRounding
open FiniteIrreducibleProfileFiniteCollection FiniteIrreduciblePearsonProfile
open FiniteIrreducibleConnectedLawFiniteSum FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleDeterministicResidualWeights
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)
open FiniteIrreducibleOddsCorrectionBounds (criticalLogOddsEnvelope criticalLogOddsEnvelope_tendsto_zero)
open FiniteIrreducibleOddsCorrectionMoments (connectedProductLaw_abs_log_oddsCorrection_ae_le)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Almost-everywhere domination is enough under the actual finite-state
laws. The required exponential moment is proved from field enumeration. -/
theorem native_pearson_with_ae_remainder_exponential_L1_limit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q)
    (lambda A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (k r : ℕ → Fin q → ℕ)
    (hk : ∀ n i, 0 < k n i)
    (pos : ∀ n i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n i) (r n i))
    (hKt : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ))
    (Q : ∀ n, StateFamily (S := S) (k n) → ℝ) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (𝓝 0))
    (hdom : ∀ᶠ n in atTop, ∀ᵐ p ∂connectedProductLaw M
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n) (r n) (pos n),
      |Q n p| ≤ (A / (n : ℝ)) * pearson M hM (k n) p + err n) :
    Tendsto (fun n ↦ ∫ p, |Real.exp (Q n p) - 1|
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
        (k n) (r n) (pos n)) atTop (𝓝 0) := by
  have hm := pearson_native_exponential_tendsto_one M hM R q hq lambda A C
    hA hC k r hk pos hKt hr hsize
  have he : Tendsto (fun n ↦ Real.exp |err n|) atTop (𝓝 1) := by
    simpa only [Function.comp_def, abs_zero, Real.exp_zero] using
      Real.continuous_exp.tendsto (|(0 : ℝ)|) |>.comp herr.abs
  have hz := (hm.mul he).sub_const 1
  simp only [mul_one, sub_self] at hz
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ integral_nonneg (fun _ ↦ abs_nonneg _)))
    _ hz
  filter_upwards [hdom] with n hn
  have hh := integral_mono_ae (μ := connectedProductLaw M
    (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n) (r n) (pos n))
    (f := fun p ↦ |Real.exp (Q n p) - 1|)
    (g := fun p ↦ Real.exp ((A / (n : ℝ)) * pearson M hM (k n) p) * Real.exp |err n| - 1)
    Integrable.of_finite Integrable.of_finite (by
      filter_upwards [hn] with p hp
      rw [← Real.exp_add]
      exact (BoundedConcentrationTransfer.abs_exp_sub_one_le_exp_abs_sub_one _).trans
        (sub_le_sub_right (Real.exp_le_exp.mpr (hp.trans
          (add_le_add le_rfl (le_abs_self _)))) 1))
  rw [integral_sub Integrable.of_finite (integrable_const 1), integral_mul_const, integral_const] at hh
  simpa only [probReal_univ, smul_eq_mul, one_mul] using hh

/-- Uniform, actual-law control of the complete normalized raw exponent.
Only literal rounded population counts and actual size/surplus bounds
are supplied. The odds term is controlled on its proved true support. -/
theorem exists_uniform_native_residual_exponent_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ) (R q : ℕ)
    (c : ℕ → S → ℕ) (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
        ∀ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
          (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i),
        (∀ i, r i ≤ R) →
        (∑ i, (k i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
        (∀ p, normalizedResidual M hM lambda n (c n) p =
          Real.exp (residualExponent M hM lambda n (c n) k p)) ∧
        (∀ᵐ p ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
            k r pos,
          |residualExponent M hM lambda n (c n) k p| ≤
            (isolationBudget M hM C 2 / (n : ℝ)) * pearson M hM k p + err n) := by
  obtain ⟨de, hde, hb⟩ := normalizedDepletion_uniform_target_remainder M c D C hD hC hround
  let pe : ℕ → ℝ := fun n ↦ populationBudget M D 2 * C * (n : ℝ) ^ (-(1 / 3 : ℝ))
  have hpe : Tendsto pe atTop (𝓝 0) := by
    simpa only [pe, Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop).const_mul (populationBudget M D 2 * C)
  let err : ℕ → ℝ := fun n ↦ de n + pe n + criticalLinearEnvelope M hM lambda C n +
    diagonalEnvelope M C n + criticalLogOddsEnvelope M 2 C q R n
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, zero_add] using
      (((hde.add hpe).add (criticalLinearEnvelope_tendsto_zero M hM lambda C)).add
        (diagonalEnvelope_tendsto_zero M C)).add (criticalLogOddsEnvelope_tendsto_zero M 2 C q R)
  have ht : ∀ᶠ n in atTop, |CriticalScaling.time lambda n| ≤ 2 := by
    have hh := (CriticalScaling.time_tendsto lambda).abs
    simp only [abs_one] at hh
    exact (hh.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))).mono (fun _ h ↦ h.le)
  refine ⟨err, herr, ?_⟩
  filter_upwards [hb, populationCorrection_uniform_log_bound M c D 2 C hD (by norm_num) hC hround,
    eventually_count_ratio_domain M c D hround,
    eventually_uniform_isolationFluctuation_bound M hM lambda C hC q, ht]
      with n hbn hpn hcn hin htn
  intro k r pos hr hs
  have hfib (p : StateFamily (S := S) k) :
      (∑ a, (fiberCount (pooledTypes p) a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) := by
    change (∑ a, pooledCountReal k p a) ≤ _
    rw [pooledCountReal_sum]
    exact hs
  refine ⟨fun p ↦ normalizedResidual_eq_exp M hM lambda hcn.1 (c n) hcn.2.1 k p
    (hbn (fiberCount (pooledTypes p)) (hfib p)).1, ?_⟩
  have ho := connectedProductLaw_abs_log_oddsCorrection_ae_le M
    (CriticalScaling.time_nonneg lambda n) ((le_abs_self _).trans htn) hcn.1 k r R
    (M.bjrModel.scalarField (CriticalScaling.time lambda n)) pos hr (by simpa only [Nat.cast_sum] using hs)
  filter_upwards [ho] with p hop
  have hd : |selectionRemainder M n (c n) p| ≤ de n :=
    (hbn (fiberCount (pooledTypes p)) (hfib p)).2
  have hp : |Real.log (populationCorrection M n (c n) (fiberCount (pooledTypes p))
      (CriticalScaling.time lambda n))| ≤ pe n :=
    (hpn (fiberCount (pooledTypes p)) (CriticalScaling.time lambda n) (hfib p) htn).2
  have hi := hin k hs p
  have hdiag := diagonalExponent_critical_bound M hcn.1 htn k p hs
  have ha : |residualExponent M hM lambda n (c n) k p| ≤
      |selectionRemainder M n (c n) p| +
      |Real.log (populationCorrection M n (c n) (fiberCount (pooledTypes p))
        (CriticalScaling.time lambda n))| +
      |isolationFluctuation M hM lambda n k p| +
      |diagonalExponent M n (CriticalScaling.time lambda n) p| +
      |Real.log (oddsCorrection M (CriticalScaling.time lambda n) n p)| := by
    unfold residualExponent
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  dsimp only [err]
  linarith

/-- L1 convergence of the literal normalized graph residual under its
native independent connected-state law, not a conditional profile law. -/
theorem native_normalizedResidual_L1_tendsto_zero
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q)
    (lambda : ℝ) (c : ℕ → S → ℕ) (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (pos : ∀ n i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n i) (r n i))
    (hKt : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun n ↦ ∫ p, |normalizedResidual M hM lambda n (c n) p - 1|
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
        (k n) (r n) (pos n)) atTop (𝓝 0) := by
  obtain ⟨err, herr, hb⟩ := exists_uniform_native_residual_exponent_bound M hM lambda R q c D C hD hC hround
  have hd : ∀ᶠ n in atTop, ∀ᵐ p ∂connectedProductLaw M
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n) (r n) (pos n),
      |residualExponent M hM lambda n (c n) (k n) p| ≤
        (isolationBudget M hM C 2 / (n : ℝ)) * pearson M hM (k n) p + err n := by
    filter_upwards [hb, hr, hsize] with n hn hrn hsn
    exact (hn (k n) (r n) (pos n) hrn hsn).2
  have hl := native_pearson_with_ae_remainder_exponential_L1_limit M hM R q hq lambda
    (isolationBudget M hM C 2) C (isolationBudget_nonneg M hM hC (by norm_num)) hC
    k r hk pos hKt hr hsize (fun n ↦ residualExponent M hM lambda n (c n) (k n)) err herr hd
  apply hl.congr'
  filter_upwards [hb, hr, hsize] with n hn hrn hsn
  apply integral_congr_ae
  exact Eventually.of_forall (fun p ↦ by
    simp only [(hn (k n) (r n) (pos n) hrn hsn).1 p])

end PerronWright.FiniteIrreducibleRawResidualAveraging
