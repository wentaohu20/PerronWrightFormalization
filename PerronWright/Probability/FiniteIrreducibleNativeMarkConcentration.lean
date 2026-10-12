import PerronWright.Probability.FiniteIrreducibleEmpiricalConcentration
import PerronWright.Probability.FiniteIrreducibleNativeProfileAveraging
import PerronWright.Probability.FiniteIrreducibleCriticalPrefactorScaling
import PerronWright.Probability.AnnealedMarkedResidualTests

/-! # Native finite empirical marks on the whole integer critical window

The marks are literal empirical probability measures of sampled
component types. Their weak-neighborhood bounds come from the actual
finite irreducible arbitrary-field estimates, with no primitive/B2
adapter. Actual pi marginals give concentration of the joint marks.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1200000

namespace PerronWright.FiniteIrreducibleNativeMarkConcentration

open FiniteIrreducibleConnectedTypeLaw (law perronLaw)
open FiniteIrreducibleEmpiricalConcentration FiniteIrreducibleNativeProfileAveraging
open FiniteIrreducibleCriticalPrefactorScaling EmpiricalWeakNeighborhood
open EmpiricalMarkConcentration (connectedMark)
open AnnealedMarkedResidualConcentration (componentMarks)
open AnnealedMarkedResidualTests (jointContinuousTestBound jointContinuousTest_abs_le)
open AnnealedMarkedResidualTransfer (measurePreserving_real_preimage_le)
open FiniteIrreducibleProfileFiniteCollection (StateFamily)
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def perronMarks (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q : ℕ) :
    Fin q → ProbabilityMeasure S := fun _ ↦ perronLaw M hM

theorem exists_uniform_single_weak_mark_envelope
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronLaw M hM)) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ k r : ℕ, ∀ hk : 0 < k,
        ∀ pos : 0 < M.bjrModel.fieldConnectedWeight
          (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r,
        a ≤ normalizedSize n k → normalizedSize n k ≤ b → r ≤ R →
        (law M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos).real
          {p | connectedMark hk p ∉ U} ≤ err n := by
  obtain ⟨L, hL, hf⟩ := exists_native_scalarField_bound M lambda b hb
  obtain ⟨F, ε, hε, hFU⟩ := exists_finite_tests_of_mem_nhds (perronLaw M hM) U hU
  let eps : (S →ᵇ ℝ) → ℝ := fun f ↦ if f ∈ F then ε f else 1
  have heps (f : S →ᵇ ℝ) : 0 < eps f := by
    dsimp only [eps]
    split_ifs with h
    · exact hε f h
    · norm_num
  choose c D hc hD ht using fun f : S →ᵇ ℝ ↦
    exists_test_exponential_bound M hM R L (eps f) hL (heps f) f.toContinuousMap
  let err : ℕ → ℝ := fun n ↦ ∑ f ∈ F, D f * Real.exp (-(c f) * (a * (n : ℝ) ^ (2 / 3 : ℝ)))
  have hpow : Tendsto (fun n : ℕ ↦ a * (n : ℝ) ^ (2 / 3 : ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop ha
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, Function.comp_def, mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum F (fun f _ ↦
        (Real.tendsto_exp_atBot.comp (hpow.const_mul_atTop_of_neg (by linarith [hc f]))).const_mul (D f))
  have hcommon := (Filter.eventually_all_finset F).mpr (fun f _ ↦ ht f)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hcommon
  refine ⟨err, herr, ?_⟩
  filter_upwards [hf, eventually_all_sizes_ge a ha K, eventually_ge_atTop (1 : ℕ)] with n hfn hkn hn1
  intro k r hk pos hka hkb hr
  have hn : 0 < n := by omega
  have hg := hfn k (size_upper_of_normalized hn hkb)
  have htests (f : S →ᵇ ℝ) (hfm : f ∈ F) :
      (law M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos).real
        {p | ε f ≤ |testDeviation M hM hk f.toContinuousMap p|} ≤
          D f * Real.exp (-(c f) * (a * (n : ℝ) ^ (2 / 3 : ℝ))) := by
    obtain ⟨hkp, hbound⟩ := hK k (hkn k hka) f hfm
    have htest := hbound r hr (M.bjrModel.scalarField (CriticalScaling.time lambda n)) hg pos
    have hmono : Real.exp (-(c f) * (k : ℝ)) ≤
        Real.exp (-(c f) * (a * (n : ℝ) ^ (2 / 3 : ℝ))) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (size_lower_of_normalized hn hka)
        (neg_nonpos.mpr (hc f).le))
    have hh : (law M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos).real
        {p | ε f ≤ |testDeviation M hM hk f.toContinuousMap p|} ≤ D f * Real.exp (-(c f) * (k : ℝ)) := by
      simpa only [eps, if_pos hfm] using htest
    exact hh.trans (mul_le_mul_of_nonneg_left hmono (hD f).le)
  have hsubset : {p | connectedMark hk p ∉ U} ⊆
      ⋃ f ∈ F, {p | ε f ≤ |testDeviation M hM hk f.toContinuousMap p|} := by
    intro p hp
    by_contra hbad
    apply hp
    apply hFU
    intro f hfm
    have hn : ¬ ε f ≤ |testDeviation M hM hk f.toContinuousMap p| := by
      intro hh
      apply hbad
      exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hfm, hh⟩⟩
    exact lt_of_not_ge hn
  exact (measureReal_mono hsubset (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le F _).trans (Finset.sum_le_sum (fun f hfm ↦ htests f hfm)))

/-- The joint empirical marks concentrate under their actual independent
native law, uniformly over every integer tuple in the size window. -/
theorem exists_uniform_joint_weak_mark_envelope
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (U : Set (Fin q → ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronMarks M hM q)) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ, ∀ hk : ∀ i, 0 < k i,
        ∀ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
          (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i),
        (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
        (∀ i, r i ≤ R) →
        (connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos).real
          {p | componentMarks hk p ∉ U} ≤ err n := by
  rw [nhds_pi] at hU
  obtain ⟨I, V, hV, hVU⟩ := Filter.mem_pi'.mp hU
  choose err herr hbound using fun i : Fin q ↦
    exists_uniform_single_weak_mark_envelope M hM R lambda a b ha hb (V i) (hV i)
  refine ⟨fun n ↦ ∑ i, err i n,
    by simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ ↦ herr i), ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with n hn
  intro k r hk pos hka hkb hr
  have heval (i : Fin q) :
      (connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos).real
        {p | componentMarks hk p i ∉ V i} ≤ err i n := by
    have he := measurePreserving_real_preimage_le (measurePreserving_eval
      (fun j ↦ law M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k j) (r j) (pos j)) i)
      {p | connectedMark (hk i) p ∉ V i}
    exact he.trans (hn i (k i) (r i) (hk i) (pos i) (hka i) (hkb i) (hr i))
  have hsub : {p : StateFamily (S := S) k | componentMarks hk p ∉ U} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin q)), {p | componentMarks hk p i ∉ V i} := by
    intro p hp
    by_contra hbad
    apply hp
    apply hVU
    intro i _
    by_contra hi
    apply hbad
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hi⟩⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le Finset.univ _).trans (Finset.sum_le_sum (fun i _ ↦ heval i)))

/-- Every continuous coupled mark test has a uniform actual L1 Perron
replacement. Compactness used for boundedness follows from finite S. -/
theorem eventually_uniform_joint_mark_test_L1
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (G : (Fin q → ProbabilityMeasure S) → ℝ) (hG : Continuous G)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ, ∀ hk : ∀ i, 0 < k i,
      ∀ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
        (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i),
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      (∫ p, |G (componentMarks hk p) - G (perronMarks M hM q)|
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) ≤ ε := by
  let B := jointContinuousTestBound G hG + |G (perronMarks M hM q)|
  have hB : 0 ≤ B := by dsimp only [B, jointContinuousTestBound]; positivity
  let U := {ν : Fin q → ProbabilityMeasure S | |G ν - G (perronMarks M hM q)| < ε / 2}
  have hU : U ∈ 𝓝 (perronMarks M hM q) := by
    apply (isOpen_lt ((hG.sub continuous_const).abs) continuous_const).mem_nhds
    change |G (perronMarks M hM q) - G (perronMarks M hM q)| < ε / 2
    simpa only [sub_self, abs_zero] using (show (0 : ℝ) < ε / 2 by positivity)
  obtain ⟨err, herr, hbnd⟩ := exists_uniform_joint_weak_mark_envelope M hM R q lambda a b ha hb U hU
  have he := (herr.const_mul B).const_add (ε / 2)
  simp only [mul_zero, add_zero] at he
  filter_upwards [hbnd, he.eventually (Iio_mem_nhds (by linarith : ε / 2 < ε))] with n hn hsmall
  intro k r hk pos hka hkb hr
  have htail := hn k r hk pos hka hkb hr
  have hdev (p : StateFamily (S := S) k) :
      |G (componentMarks hk p) - G (perronMarks M hM q)| ≤ B :=
    (abs_sub _ _).trans (add_le_add (jointContinuousTest_abs_le G hG _) le_rfl)
  have hi := BoundedConcentrationTransfer.integral_abs_le_threshold_tail
    (connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos)
    (fun p ↦ G (componentMarks hk p) - G (perronMarks M hM q))
    (measurable_of_countable _) hB (by positivity : (0 : ℝ) ≤ ε / 2) hdev
  have ht : (connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos).real
      {p | ε / 2 ≤ |G (componentMarks hk p) - G (perronMarks M hM q)|} ≤ err n := by
    simpa only [U, Set.mem_ofPred_eq, not_lt] using htail
  exact hi.trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_left ht hB)).trans hsmall.le)

end PerronWright.FiniteIrreducibleNativeMarkConcentration
