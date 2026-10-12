import PerronWright.Probability.FiniteIrreducibleOddsCorrectionMoments
import PerronWright.Probability.FiniteIrreducibleProfileLaplace
import PerronWright.Probability.FiniteIrreducibleCriticalPrefactorScaling

/-!
# Genuine finite critical-window negligibility of the odds correction

All positive connected-law normalizers in the main endpoints are obtained
from the proved finite irreducible enumeration. The bounds and actual
moment convergence are uniform over the complete type-profile space and
over bounded surpluses and positive bounded times. No B2, typical-profile,
or residual-isolation assumption is used.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology Real
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleOddsCorrectionTerminal

open AnnealedTupleResidualConnectedLawProduct FiniteIrreducibleDeterministicResidualWeights
open FiniteIrreducibleProfileFiniteCollection FiniteIrreducibleDeterministicConnectedLawFormula
open FiniteIrreducibleOddsCorrectionBounds FiniteIrreducibleOddsCorrectionMoments
open FiniteIrreducibleCriticalPrefactorScaling

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Enumeration supplies actual probability laws; their odds L1 and mean
bounds then follow for every eligible graph and every type profile. -/
theorem exists_large_size_productLaw_odds_bounds
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (T C : ℝ) :
    ∃ K : ℕ, 0 < K ∧ ∀ {n : ℕ}, 0 < n → ∀ k r : Fin q → ℕ,
      (∀ i, K ≤ k i) → (∀ i, r i ≤ R) → ∀ g : Fin q → C(S,ℝ),
      ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ((∑ i, k i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ) →
      ∃ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i),
        (∫ p, |oddsCorrection M t n p-1| ∂productLaw M k r g pos) ≤
          criticalOddsEnvelope M T C q R n ∧
        |(∫ p, oddsCorrection M t n p ∂productLaw M k r g pos)-1| ≤
          criticalOddsEnvelope M T C q R n := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (FiniteIrreducibleProfileLaplace.eventually_all_field_normalizers_pos M hM R)
  refine ⟨max 1 K, by omega, ?_⟩
  intro n hn k r hk hr g t ht htT hsize
  have pos (i : Fin q) : 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i) :=
    hK (k i) ((le_max_right 1 K).trans (hk i)) (r i) (hr i) (g i)
  exact ⟨pos, productLaw_integral_abs_oddsCorrection_sub_one_le M ht htT hn k r R g pos hr hsize,
    productLaw_integral_oddsCorrection_sub_one_abs_le M ht htT hn k r R g pos hr hsize⟩

/-- No normalization premise is present: a common full integer-size
window threshold supplies genuine laws and uniform vanishing moments. -/
theorem eventually_uniform_productLaw_odds_moments
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (T a b : ℝ) (ha : 0 < a) (_hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) → ∀ g : Fin q → C(S,ℝ), ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ∃ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (g i) (k i) (r i),
        (∫ p, |oddsCorrection M t n p-1| ∂productLaw M k r g pos) ≤ ε ∧
        |(∫ p, oddsCorrection M t n p ∂productLaw M k r g pos)-1| ≤ ε := by
  let C : ℝ := (q : ℝ) * b
  obtain ⟨K, _hK, hbound⟩ := exists_large_size_productLaw_odds_bounds M hM q R T C
  filter_upwards [eventually_all_sizes_ge a ha K, eventually_ge_atTop (1 : ℕ),
    (criticalOddsEnvelope_tendsto_zero M T C q R).eventually (Iio_mem_nhds hε)]
    with n hge hn1 he k r hka hkb hr g t ht htT
  have hsize : ((∑ i, k i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ _i : Fin q, b * (n : ℝ)^(2/3 : ℝ) :=
        Finset.sum_le_sum (fun i _ ↦ size_upper_of_normalized (by omega) (hkb i))
      _ = _ := by simp [C, mul_assoc]
  obtain ⟨pos, hL1, hmean⟩ :=
    hbound (by omega) k r (fun i ↦ hge (k i) (hka i)) hr g t ht htT hsize
  exact ⟨pos, hL1.trans he.le, hmean.trans he.le⟩

theorem eventually_uniform_connectedProductLaw_odds_moments
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (T a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) → ∀ g : C(S,ℝ), ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ∃ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight g (k i) (r i),
        (∫ p, |oddsCorrection M t n p-1| ∂connectedProductLaw M g k r pos) ≤ ε ∧
        |(∫ p, oddsCorrection M t n p ∂connectedProductLaw M g k r pos)-1| ≤ ε := by
  filter_upwards [eventually_uniform_productLaw_odds_moments M hM q R T a b ha hb hε]
    with n hn k r hka hkb hr g t ht htT
  obtain ⟨pos, hL1, hmean⟩ := hn k r hka hkb hr (fun _ ↦ g) t ht htT
  exact ⟨pos, by simpa only [connectedProductLaw_eq_productLaw] using hL1,
    by simpa only [connectedProductLaw_eq_productLaw] using hmean⟩

/-- In particular the literal paper critical time requires no supplied
bounded-time or normalizer premise at the eventual local window. -/
theorem eventually_uniform_critical_time_odds_moments
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      ∃ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
          (M.bjrModel.scalarField (rawTime lambda n)) (k i) (r i),
        (∫ p, |oddsCorrection M (rawTime lambda n) n p-1|
          ∂connectedProductLaw M (M.bjrModel.scalarField (rawTime lambda n)) k r pos) ≤ ε ∧
        |(∫ p, oddsCorrection M (rawTime lambda n) n p
          ∂connectedProductLaw M (M.bjrModel.scalarField (rawTime lambda n)) k r pos)-1| ≤ ε := by
  filter_upwards [eventually_uniform_connectedProductLaw_odds_moments M hM q R 2 a b ha hb hε,
    (rawTime_tendsto lambda).eventually
      (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))]
    with n hn ht k r hka hkb hr
  exact hn k r hka hkb hr _ _ ht.1.le ht.2.le

/-- Moving genuine product laws are constructed on an actual finite tail.
Their L1 and expectation limits are proved, not assumed through a
positive-normalizer or typical-profile convergence interface. -/
theorem exists_tail_productLaw_odds_L1_and_mean_tendsto
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ}
    (R : ℕ) (T C : ℝ) (k r : ℕ → Fin q → ℕ)
    (t : ℕ → ℝ) (g : ℕ → Fin q → C(S,ℝ))
    (hk : ∀ i, Tendsto (fun n ↦ k n i) atTop atTop)
    (ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ T)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hsize : ∀ᶠ n in atTop, ((∑ i, k n i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)) :
    ∃ J : ℕ, ∃ pos : ∀ m i,
        0 < M.bjrModel.fieldConnectedWeight (g (J+m) i) (k (J+m) i) (r (J+m) i),
      Tendsto (fun m ↦ ∫ p, |oddsCorrection M (t (J+m)) (J+m) p-1|
        ∂productLaw M (k (J+m)) (r (J+m)) (g (J+m)) (pos m)) atTop (𝓝 0) ∧
      Tendsto (fun m ↦ ∫ p, oddsCorrection M (t (J+m)) (J+m) p
        ∂productLaw M (k (J+m)) (r (J+m)) (g (J+m)) (pos m)) atTop (𝓝 1) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (FiniteIrreducibleProfileLaplace.eventually_all_field_normalizers_pos M hM R)
  have hge : ∀ᶠ n in atTop, ∀ i, K ≤ k n i :=
    eventually_all.mpr (fun i ↦ (hk i).eventually (eventually_ge_atTop K))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hge.and hr)
  have pos (m : ℕ) (i : Fin q) :
      0 < M.bjrModel.fieldConnectedWeight (g (J+m) i) (k (J+m) i) (r (J+m) i) :=
    hK _ ((hJ (J+m) (by omega)).1 i) _ ((hJ (J+m) (by omega)).2 i) _
  have htail : Tendsto (fun m : ℕ ↦ J+m) atTop atTop := by
    simpa only [add_comm] using tendsto_add_atTop_nat J
  refine ⟨J, pos, ?_⟩
  exact oddsCorrection_productLaw_L1_and_mean_tendsto M R T C (fun m ↦ J+m) htail
    (fun m ↦ k (J+m)) (fun m ↦ r (J+m)) (fun m ↦ t (J+m)) (fun m ↦ g (J+m)) pos
    (htail.eventually ht) (htail.eventually hr) (htail.eventually hsize)

theorem exists_tail_connectedProductLaw_odds_L1_and_mean_tendsto
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ}
    (R : ℕ) (T C : ℝ) (k r : ℕ → Fin q → ℕ)
    (t : ℕ → ℝ) (g : ℕ → C(S,ℝ))
    (hk : ∀ i, Tendsto (fun n ↦ k n i) atTop atTop)
    (ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ T)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hsize : ∀ᶠ n in atTop, ((∑ i, k n i : ℕ) : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)) :
    ∃ J : ℕ, ∃ pos : ∀ m i,
        0 < M.bjrModel.fieldConnectedWeight (g (J+m)) (k (J+m) i) (r (J+m) i),
      Tendsto (fun m ↦ ∫ p, |oddsCorrection M (t (J+m)) (J+m) p-1|
        ∂connectedProductLaw M (g (J+m)) (k (J+m)) (r (J+m)) (pos m)) atTop (𝓝 0) ∧
      Tendsto (fun m ↦ ∫ p, oddsCorrection M (t (J+m)) (J+m) p
        ∂connectedProductLaw M (g (J+m)) (k (J+m)) (r (J+m)) (pos m)) atTop (𝓝 1) := by
  obtain ⟨J, pos, hL1, hmean⟩ := exists_tail_productLaw_odds_L1_and_mean_tendsto M hM R T C k r t
    (fun n _ ↦ g n) hk ht hr hsize
  exact ⟨J, pos, by simpa only [connectedProductLaw_eq_productLaw] using hL1,
    by simpa only [connectedProductLaw_eq_productLaw] using hmean⟩

end PerronWright.FiniteIrreducibleOddsCorrectionTerminal

