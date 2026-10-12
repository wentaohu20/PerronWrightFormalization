import PerronWright.Probability.FiniteIrreducibleResidualNormalization
import PerronWright.Probability.FiniteIrreducibleVaryingIsolation

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

namespace PerronWright.FiniteIrreducibleVaryingResidualExponent

open FiniteIrreducibleVaryingCriticalTime FiniteIrreducibleVaryingIsolation
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

/-- Uniform, actual-law control of the complete normalized raw exponent.
Only literal rounded population counts and actual size/surplus bounds
are supplied. The odds term is controlled on its proved true support. -/
theorem exists_uniform_native_residual_exponent_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell : ℕ → ℝ) (lambda : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) (R q : ℕ)
    (c : ℕ → S → ℕ) (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
        ∀ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
          (M.bjrModel.scalarField (CriticalScaling.time (ell n) n)) (k i) (r i),
        (∀ i, r i ≤ R) →
        (∑ i, (k i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
        (∀ p, normalizedResidual M hM (ell n) n (c n) p =
          Real.exp (residualExponent M hM (ell n) n (c n) k p)) ∧
        (∀ᵐ p ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time (ell n) n))
            k r pos,
          |residualExponent M hM (ell n) n (c n) k p| ≤
            (isolationBudget M hM C 2 / (n : ℝ)) * pearson M hM k p + err n) := by
  obtain ⟨de, hde, hb⟩ := normalizedDepletion_uniform_target_remainder M c D C hD hC hround
  let pe : ℕ → ℝ := fun n ↦ populationBudget M D 2 * C * (n : ℝ) ^ (-(1 / 3 : ℝ))
  have hpe : Tendsto pe atTop (𝓝 0) := by
    simpa only [pe, Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop).const_mul (populationBudget M D 2 * C)
  let err : ℕ → ℝ := fun n ↦ de n + pe n + criticalLinearEnvelope M hM (|lambda| + 1) C n +
    diagonalEnvelope M C n + criticalLogOddsEnvelope M 2 C q R n
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, zero_add] using
      (((hde.add hpe).add (criticalLinearEnvelope_tendsto_zero M hM (|lambda| + 1) C)).add
        (diagonalEnvelope_tendsto_zero M C)).add (criticalLogOddsEnvelope_tendsto_zero M 2 C q R)
  have ht := eventually_time_abs_le_two ell lambda hl
  refine ⟨err, herr, ?_⟩
  filter_upwards [hb, populationCorrection_uniform_log_bound M c D 2 C hD (by norm_num) hC hround,
    eventually_count_ratio_domain M c D hround,
    FiniteIrreducibleVaryingIsolation.eventually_uniform_isolationFluctuation_bound M hM ell lambda C hl hC q, ht]
      with n hbn hpn hcn hin htn
  intro k r pos hr hs
  have hfib (p : StateFamily (S := S) k) :
      (∑ a, (fiberCount (pooledTypes p) a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) := by
    change (∑ a, pooledCountReal k p a) ≤ _
    rw [pooledCountReal_sum]
    exact hs
  refine ⟨fun p ↦ normalizedResidual_eq_exp M hM (ell n) hcn.1 (c n) hcn.2.1 k p
    (hbn (fiberCount (pooledTypes p)) (hfib p)).1, ?_⟩
  have ho := connectedProductLaw_abs_log_oddsCorrection_ae_le M
    (CriticalScaling.time_nonneg (ell n) n) ((le_abs_self _).trans htn) hcn.1 k r R
    (M.bjrModel.scalarField (CriticalScaling.time (ell n) n)) pos hr (by simpa only [Nat.cast_sum] using hs)
  filter_upwards [ho] with p hop
  have hd : |selectionRemainder M n (c n) p| ≤ de n :=
    (hbn (fiberCount (pooledTypes p)) (hfib p)).2
  have hp : |Real.log (populationCorrection M n (c n) (fiberCount (pooledTypes p))
      (CriticalScaling.time (ell n) n))| ≤ pe n :=
    (hpn (fiberCount (pooledTypes p)) (CriticalScaling.time (ell n) n) (hfib p) htn).2
  have hi := hin k hs p
  have hdiag := diagonalExponent_critical_bound M hcn.1 htn k p hs
  have ha : |residualExponent M hM (ell n) n (c n) k p| ≤
      |selectionRemainder M n (c n) p| +
      |Real.log (populationCorrection M n (c n) (fiberCount (pooledTypes p))
        (CriticalScaling.time (ell n) n))| +
      |isolationFluctuation M hM (ell n) n k p| +
      |diagonalExponent M n (CriticalScaling.time (ell n) n) p| +
      |Real.log (oddsCorrection M (CriticalScaling.time (ell n) n) n p)| := by
    unfold residualExponent
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  dsimp only [err]
  linarith


end PerronWright.FiniteIrreducibleVaryingResidualExponent
