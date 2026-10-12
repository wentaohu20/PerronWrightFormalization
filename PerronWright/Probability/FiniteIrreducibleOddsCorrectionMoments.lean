import PerronWright.Probability.FiniteIrreducibleOddsCorrectionBounds
import PerronWright.Probability.FiniteIrreducibleProfileFiniteCollection
import PerronWright.Probability.FiniteIrreducibleDeterministicConnectedLawFormula
import PerronWright.Probability.ConnectedTypeTails

/-!
# Genuine connected-product support and odds moments

Eligibility is proved from each literal connected-law density and the
actual product measure. The finite state spaces give genuine integrability.
Thus the all-profile odds bounds imply actual L1 and expectation bounds.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology Real
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleOddsCorrectionMoments

open AnnealedTupleResidualConnectedLawProduct FiniteIrreducibleDeterministicResidualWeights
open FiniteIrreducibleProfileFiniteCollection FiniteIrreducibleDeterministicConnectedLawFormula
open FiniteIrreducibleOddsCorrectionBounds

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem connectedLaw_eligible_ae (M : FiniteIrreducibleModel S) (g : C(S,ℝ))
    (k r : ℕ) (hC : 0 < M.bjrModel.fieldConnectedWeight g k r) :
    ∀ᵐ p ∂FiniteIrreducibleConnectedTypeLaw.law M g k r hC,
      ConnectedTypeLaw.Eligible r p.2 :=
  ConnectedTypeLaw.eligible_ae M.bjrModel g k r hC

theorem productLaw_eligible_ae (M : FiniteIrreducibleModel S) {q : ℕ}
    (k r : Fin q → ℕ) (g : Fin q → C(S,ℝ))
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i)) :
    ∀ᵐ p ∂productLaw M k r g hC, ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun j ↦
    FiniteIrreducibleConnectedTypeLaw.law M (g j) (k j) (r j) (hC j)) i).quasiMeasurePreserving.ae
    (connectedLaw_eligible_ae M (g i) (k i) (r i) (hC i))

theorem productLaw_totalEdges_ae (M : FiniteIrreducibleModel S) {q : ℕ}
    (k r : Fin q → ℕ) (g : Fin q → C(S,ℝ))
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i)) :
    ∀ᵐ p ∂productLaw M k r g hC, totalEdges p = ∑ i, (k i+r i-1) := by
  filter_upwards [productLaw_eligible_ae M k r g hC] with p hp
  exact totalEdges_eq_surplus k r p hp

theorem connectedProductLaw_eq_productLaw (M : FiniteIrreducibleModel S)
    (g : C(S,ℝ)) {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight g (k i) (r i)) :
    connectedProductLaw M g k r hC = productLaw M k r (fun _ ↦ g) hC := rfl

theorem connectedProductLaw_eligible_ae (M : FiniteIrreducibleModel S)
    (g : C(S,ℝ)) {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight g (k i) (r i)) :
    ∀ᵐ p ∂connectedProductLaw M g k r hC,
      ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2 := by
  rw [connectedProductLaw_eq_productLaw]
  exact productLaw_eligible_ae M k r (fun _ ↦ g) hC

theorem oddsCorrection_integrable_productLaw (M : FiniteIrreducibleModel S)
    (t : ℝ) (n : ℕ) {q : ℕ} (k r : Fin q → ℕ) (g : Fin q → C(S,ℝ))
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i)) :
    Integrable (oddsCorrection M t n) (productLaw M k r g hC) := Integrable.of_finite

theorem productLaw_abs_log_oddsCorrection_ae_le
    (M : FiniteIrreducibleModel S) {t T C : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    {n : ℕ} (hn : 0 < n) {q : ℕ} (k r : Fin q → ℕ) (R : ℕ)
    (g : Fin q → C(S,ℝ))
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i))
    (hr : ∀ i, r i ≤ R)
    (hsize : ((∑ i, k i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)) :
    ∀ᵐ p ∂productLaw M k r g hC, |Real.log (oddsCorrection M t n p)| ≤
      criticalLogOddsEnvelope M T C q R n := by
  filter_upwards [productLaw_eligible_ae M k r g hC] with p hp
  have h := log_oddsCorrection_critical_window_bound M ht htT hn k r R p hp hr hsize
  rw [abs_of_nonneg h.1]
  exact h.2

theorem connectedProductLaw_abs_log_oddsCorrection_ae_le
    (M : FiniteIrreducibleModel S) {t T C : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    {n : ℕ} (hn : 0 < n) {q : ℕ} (k r : Fin q → ℕ) (R : ℕ) (g : C(S,ℝ))
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight g (k i) (r i))
    (hr : ∀ i, r i ≤ R)
    (hsize : ((∑ i, k i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)) :
    ∀ᵐ p ∂connectedProductLaw M g k r hC, |Real.log (oddsCorrection M t n p)| ≤
      criticalLogOddsEnvelope M T C q R n := by
  rw [connectedProductLaw_eq_productLaw]
  exact productLaw_abs_log_oddsCorrection_ae_le M ht htT hn k r R (fun _ ↦ g) hC hr hsize

theorem productLaw_integral_abs_oddsCorrection_sub_one_le
    (M : FiniteIrreducibleModel S) {t T C : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    {n : ℕ} (hn : 0 < n) {q : ℕ} (k r : Fin q → ℕ) (R : ℕ)
    (g : Fin q → C(S,ℝ))
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i))
    (hr : ∀ i, r i ≤ R)
    (hsize : ((∑ i, k i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)) :
    (∫ p, |oddsCorrection M t n p - 1| ∂productLaw M k r g hC) ≤
      criticalOddsEnvelope M T C q R n := by
  have hbound : ∀ᵐ p ∂productLaw M k r g hC,
      |oddsCorrection M t n p-1| ≤ criticalOddsEnvelope M T C q R n := by
    filter_upwards [productLaw_eligible_ae M k r g hC] with p hp
    exact oddsCorrection_critical_window_bound M ht htT hn k r R p hp hr hsize
  have h := integral_mono_ae
    (Integrable.of_finite : Integrable (fun p ↦ |oddsCorrection M t n p-1|)
      (productLaw M k r g hC)) (integrable_const _) hbound
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem productLaw_integral_oddsCorrection_sub_one_abs_le
    (M : FiniteIrreducibleModel S) {t T C : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    {n : ℕ} (hn : 0 < n) {q : ℕ} (k r : Fin q → ℕ) (R : ℕ)
    (g : Fin q → C(S,ℝ))
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i))
    (hr : ∀ i, r i ≤ R)
    (hsize : ((∑ i, k i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)) :
    |(∫ p, oddsCorrection M t n p ∂productLaw M k r g hC)-1| ≤
      criticalOddsEnvelope M T C q R n := by
  have h := abs_integral_le_integral_abs (μ := productLaw M k r g hC)
    (f := fun p ↦ oddsCorrection M t n p-1)
  rw [integral_sub (oddsCorrection_integrable_productLaw M t n k r g hC)
    (integrable_const 1), integral_const] at h
  have h' : |(∫ p, oddsCorrection M t n p ∂productLaw M k r g hC)-1| ≤
      ∫ p, |oddsCorrection M t n p-1| ∂productLaw M k r g hC := by
    simpa only [probReal_univ, smul_eq_mul, one_mul] using h
  exact h'.trans (productLaw_integral_abs_oddsCorrection_sub_one_le M ht htT hn k r R g hC hr hsize)

/-- Actual moment convergence for any genuine connected-product laws,
without a profile restriction. The hC terms are proof data defining those
laws; the separate critical-window terminal derives them from enumeration. -/
theorem oddsCorrection_productLaw_L1_and_mean_tendsto
    (M : FiniteIrreducibleModel S) {q : ℕ} (R : ℕ) (T C : ℝ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (k r : ℕ → Fin q → ℕ)
    (t : ℕ → ℝ) (g : ℕ → Fin q → C(S,ℝ))
    (pos : ∀ m i, 0 < M.bjrModel.fieldConnectedWeight (g m i) (k m i) (r m i))
    (ht : ∀ᶠ m in atTop, 0 ≤ t m ∧ t m ≤ T)
    (hr : ∀ᶠ m in atTop, ∀ i, r m i ≤ R)
    (hsize : ∀ᶠ m in atTop, ((∑ i, k m i : ℕ) : ℝ) ≤ C * (N m : ℝ)^(2/3 : ℝ)) :
    Tendsto (fun m ↦ ∫ p, |oddsCorrection M (t m) (N m) p-1|
      ∂productLaw M (k m) (r m) (g m) (pos m)) atTop (𝓝 0) ∧
    Tendsto (fun m ↦ ∫ p, oddsCorrection M (t m) (N m) p
      ∂productLaw M (k m) (r m) (g m) (pos m)) atTop (𝓝 1) := by
  have hE := (criticalOddsEnvelope_tendsto_zero M T C q R).comp hN
  have hL1 : Tendsto (fun m ↦ ∫ p, |oddsCorrection M (t m) (N m) p-1|
      ∂productLaw M (k m) (r m) (g m) (pos m)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))) _ hE
    filter_upwards [hN.eventually (eventually_ge_atTop (1 : ℕ)), ht, hr, hsize]
      with m hn htm hrm hsm
    exact productLaw_integral_abs_oddsCorrection_sub_one_le M htm.1 htm.2 (by omega)
      (k m) (r m) R (g m) (pos m) hrm hsm
  have hmean : Tendsto (fun m ↦ ∫ p, oddsCorrection M (t m) (N m) p
      ∂productLaw M (k m) (r m) (g m) (pos m)) atTop (𝓝 1) := by
    have habs : Tendsto (fun m ↦ |(∫ p, oddsCorrection M (t m) (N m) p
        ∂productLaw M (k m) (r m) (g m) (pos m))-1|) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hE
      filter_upwards [hN.eventually (eventually_ge_atTop (1 : ℕ)), ht, hr, hsize]
        with m hn htm hrm hsm
      exact productLaw_integral_oddsCorrection_sub_one_abs_le M htm.1 htm.2 (by omega)
        (k m) (r m) R (g m) (pos m) hrm hsm
    simpa only [Real.norm_eq_abs] using (tendsto_iff_norm_sub_tendsto_zero.mpr habs)
  exact ⟨hL1, hmean⟩

end PerronWright.FiniteIrreducibleOddsCorrectionMoments

