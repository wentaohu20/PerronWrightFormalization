import PerronWright.Probability.FiniteIrreducibleNativeMarkConcentration
import PerronWright.Probability.FiniteIrreducibleRawResidualUniform

/-! # Genuine finite residual-weighted joint Perron marks

The actual connected-law mark concentration and the actual normalized
raw-residual L1 estimate are combined. No concentration, weighted-law,
or uniform-integrability interface is an assumption of the terminal.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1200000

namespace PerronWright.FiniteIrreducibleMarkedResidualTransfer

open FiniteIrreducibleNativeMarkConcentration FiniteIrreducibleResidualNormalization
open FiniteIrreducibleRawResidualUniform FiniteIrreducibleCriticalPrefactorScaling
open AnnealedMarkedResidualConcentration (componentMarks)
open AnnealedMarkedResidualTests (jointContinuousTestBound jointContinuousTest_abs_le)
open AnnealedMarkedResidualTransfer (integral_weighted_test_sub_le)
open FiniteIrreducibleProfileFiniteCollection (StateFamily)
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem joint_mark_integral_error_le {q : ℕ} {k r : Fin q → ℕ}
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ) (n : ℕ)
    (hk : ∀ i, 0 < k i)
    (pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i))
    (G : (Fin q → ProbabilityMeasure S) → ℝ) :
    |(∫ p, G (componentMarks hk p)
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) -
      G (perronMarks M hM q)| ≤
      ∫ p, |G (componentMarks hk p) - G (perronMarks M hM q)|
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos := by
  have hh := abs_integral_le_integral_abs
    (μ := connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos)
    (f := fun p ↦ G (componentMarks hk p) - G (perronMarks M hM q))
  rw [integral_sub Integrable.of_finite (integrable_const _), integral_const] at hh
  simpa only [probReal_univ, smul_eq_mul, one_mul] using hh

/-- A genuine model-only uniform replacement of the empirical joint mark
test by its literal canonical Perron value in the complete raw residual
integral. Arbitrary coupled continuous tests, not just products, work. -/
theorem eventually_uniform_weighted_joint_mark_test
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (G : (Fin q → ProbabilityMeasure S) → ℝ) (hG : Continuous G)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      ∃ hk : ∀ i, 0 < k i,
      ∃ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
        (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i),
        |(∫ p, normalizedResidual M hM lambda n (c n) p * G (componentMarks hk p)
          ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) -
          G (perronMarks M hM q)| ≤ ε := by
  let B := jointContinuousTestBound G hG
  have hB : 0 ≤ B := by dsimp only [B, jointContinuousTestBound]; positivity
  let δ : ℝ := ε / (2 * (B + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [eventually_uniform_native_rawResidual_limits M hM R q hq lambda a b ha hb c D hD hround hδ,
    eventually_uniform_joint_mark_test_L1 M hM R q lambda a b ha hb G hG
      (show 0 < ε / 2 by positivity),
    eventually_all_sizes_ge a ha 1] with n hres hmark hsize
  intro k r hka hkb hr
  have hk : ∀ i, 0 < k i := fun i ↦ by have := hsize (k i) (hka i); omega
  obtain ⟨pos, hL, _⟩ := hres k r hka hkb hr
  refine ⟨hk, pos, ?_⟩
  have htest := integral_weighted_test_sub_le
    (connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos)
    (fun p ↦ normalizedResidual M hM lambda n (c n) p) (fun p ↦ G (componentMarks hk p))
    Integrable.of_finite (measurable_of_countable _) (fun p ↦ jointContinuousTest_abs_le G hG _)
  have hbase := (joint_mark_integral_error_le M hM lambda n hk pos G).trans
    (hmark k r hk pos hka hkb hr)
  have hweighted : |(∫ p, normalizedResidual M hM lambda n (c n) p * G (componentMarks hk p)
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) -
      ∫ p, G (componentMarks hk p)
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos| ≤ ε / 2 := by
    refine htest.trans ((mul_le_mul_of_nonneg_left hL hB).trans ?_)
    dsimp only [δ]
    have hb : B / (B + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    calc
      _ = (ε / 2) * (B / (B + 1)) := by field_simp
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ε / 2 := by ring
  exact (abs_sub_le _ _ _).trans (by linarith [hweighted, hbase])

end PerronWright.FiniteIrreducibleMarkedResidualTransfer
