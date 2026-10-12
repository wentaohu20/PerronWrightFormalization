import PerronWright.Probability.BrownianExcursionTupleTests
import PerronWright.Probability.ComponentWindowMixedFactorials
import PerronWright.Probability.CountableFiniteTupleSampling
import PerronWright.Probability.SizeCellIndicators

/-! # Canonical Brownian window cell factorials as actual labelled tuples

Finite-atom cardinality, rather than distinctness of atom positions,
retains multiplicities. The finite surplus expansion uses the literal
independent Poisson count coordinates of the constructed Brownian source.
No moment, density, or point-process identification is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianWindowCellTupleGeometry

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionSection
open BrownianExcursionWindowPointMeasure BrownianExcursionPointProcessLaw
open BrownianExcursionTupleTests BrownianFullHorizonPoissonMarks
open ComponentGlobalPointProcess ComponentWindowMixedFactorials
open ComponentWindowPointMeasures PositiveSizeSurplusExhaustion GlobalPointMeasureCharts
open FinitePointMeasureCompact FinitePointMeasureMixedFactorials FactorialCountDeterminacy
open SizeCellIndicators

variable {D : Type*} [Fintype D]

def mixedStatistic (m : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (η : Chart m) : ℝ :=
  factorialPolynomial q (fun i ↦ count η
    (windowEmbedding (lower m) (upper m) m ⁻¹' sizeSurplusCells J S i))

theorem measurable_mixedStatistic (m : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (q : D → ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    Measurable (mixedStatistic m J S q) :=
  measurable_window_mixed_factorial (lower m) (upper m) m _ q
    (fun i ↦ (measurable_windowEmbedding _ _ _) (measurableSet_sizeSurplusCells J S hJ i))

theorem mixedStatistic_nonneg (m : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (q : D → ℕ) (η : Chart m) : 0 ≤ mixedStatistic m J S q η := by
  exact Finset.prod_nonneg (fun _ _ ↦ Nat.cast_nonneg _)

private def lengthCellTest (J : D → Set ℝ) (q : D → ℕ)
    (z : Fin (∑ i, q i) → PositiveSizeSurplus) : ℝ≥0∞ :=
  ENNReal.ofReal (cellWeight (fun j ↦ J (label q j)) (fun j ↦ (z j).1.val))

private theorem measurable_lengthCellTest (J : D → Set ℝ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) : Measurable (lengthCellTest J q) := by
  apply ((measurable_cellWeight _ (fun j ↦ hJ (label q j))).comp _).ennreal_ofReal
  exact measurable_pi_lambda _ (fun j ↦
    measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply j)))

omit [Fintype D] in
private theorem selected_cell_iff (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (p : Path × (ℕ → ℕ))
    (hg : Good lambda p.1) (i : D) (e : ℚ) :
    (e ∈ selected lambda m (pathInput p) ∧
      windowAtom lambda m e (pathInput p) ∈
        windowEmbedding (lower m) (upper m) m ⁻¹' sizeSurplusCells J S i) ↔
      Representative (driftedReflectionPath lambda p.1) e ∧
      lengthValue lambda e p.1 ∈ Icc (lower m) (upper m) ∧
      lengthValue lambda e p.1 ∈ J i ∧
      rationalCount p.2 e ≤ m ∧ rationalCount p.2 e ∈ S i := by
  constructor
  · rintro ⟨hs,hc⟩
    have hv := windowAtom_eq lambda m e (pathInput p) hs
    change (windowAtom lambda m e (pathInput p)).1.val ∈ J i ∧
      (windowAtom lambda m e (pathInput p)).2.val ∈ S i at hc
    rw [hv.1,hv.2] at hc
    exact ⟨hs.2.1,hs.2.2.1,hc.1,hs.2.2.2,hc.2⟩
  · rintro ⟨hr,hb,hJ,hm,hS⟩
    have hs : e ∈ selected lambda m (pathInput p) := ⟨hg,hr,hb,hm⟩
    refine ⟨hs,?_⟩
    have hv := windowAtom_eq lambda m e (pathInput p) hs
    change (windowAtom lambda m e (pathInput p)).1.val ∈ J i ∧
      (windowAtom lambda m e (pathInput p)).2.val ∈ S i
    rw [hv.1,hv.2]
    exact ⟨hJ,hS⟩

private theorem contribution_indicator (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (q : D → ℕ) (r : Fin (∑ i, q i) → ℕ)
    (e : Fin (∑ i, q i) → ℚ) (p : Path × (ℕ → ℕ)) :
    contribution lambda (fun _ ↦ lower m) (fun _ ↦ upper m) r
      (lengthCellTest J q) e p =
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda
        (fun _ ↦ lower m) (fun _ ↦ upper m) e p.1 ∧
        (∀ j, rationalCount p.2 (e j) = r j) ∧
        (∀ j, lengthValue lambda (e j) p.1 ∈ J (label q j)) then 1 else 0 := by
  by_cases he : BrownianExcursionTuplePoissonWeights.sourceEvent lambda
      (fun _ ↦ lower m) (fun _ ↦ upper m) e p.1 ∧
      ∀ j, rationalCount p.2 (e j) = r j
  · have hp (j) : 0 < lengthValue lambda (e j) p.1 :=
      (lower_pos m).trans_le ((he.1.2 j).2.1)
    have hv := funext (markedTuple_size lambda r e p.1 hp)
    simp only [contribution,BrownianExcursionTuplePoissonWeights.contribution,
      if_pos he,one_mul,lengthCellTest,hv,cellWeight_eq]
    by_cases hJ : ∀ j, lengthValue lambda (e j) p.1 ∈ J (label q j)
    · simp [he.1,he.2,hJ]
    · simp [he.1,he.2,hJ]
  · have hh : ¬ (BrownianExcursionTuplePoissonWeights.sourceEvent lambda
        (fun _ ↦ lower m) (fun _ ↦ upper m) e p.1 ∧
        (∀ j, rationalCount p.2 (e j) = r j) ∧
        (∀ j, lengthValue lambda (e j) p.1 ∈ J (label q j))) :=
      fun h ↦ he ⟨h.1,h.2.1⟩
    simp only [contribution,BrownianExcursionTuplePoissonWeights.contribution,
      if_neg he,zero_mul,if_neg hh]

private theorem contribution_sum (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (e : Fin (∑ i, q i) → ℚ) (p : Path × (ℕ → ℕ)) :
    (∑ r ∈ cellSurplusIndices m S q,
      contribution lambda (fun _ ↦ lower m) (fun _ ↦ upper m) r
        (lengthCellTest J q) e p) =
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda
        (fun _ ↦ lower m) (fun _ ↦ upper m) e p.1 ∧
        (∀ j, lengthValue lambda (e j) p.1 ∈ J (label q j)) ∧
        (∀ j, rationalCount p.2 (e j) ≤ m ∧ rationalCount p.2 (e j) ∈ S (label q j))
      then 1 else 0 := by
  let r0 : Fin (∑ i, q i) → ℕ := fun j ↦ rationalCount p.2 (e j)
  have hr (r : Fin (∑ i, q i) → ℕ) : (∀ j, rationalCount p.2 (e j) = r j) ↔ r = r0 := by
    constructor
    · intro h
      exact (funext h).symm
    · rintro rfl
      exact fun _ ↦ rfl
  simp_rw [contribution_indicator,hr]
  by_cases h0 : r0 ∈ cellSurplusIndices m S q
  · rw [Finset.sum_eq_single r0]
    · have h0' : ∀ j, rationalCount p.2 (e j) ≤ m ∧ rationalCount p.2 (e j) ∈ S (label q j) :=
        (mem_cellSurplusIndices m S q r0).mp h0
      simp [h0']
    · intro r _ hne
      simp [hne]
    · exact fun hn ↦ (hn h0).elim
  · have h0' : ¬ ∀ j, rationalCount p.2 (e j) ≤ m ∧ rationalCount p.2 (e j) ∈ S (label q j) :=
      mt (mem_cellSurplusIndices m S q r0).mpr h0
    simp only [h0',and_false,if_false]
    apply Finset.sum_eq_zero
    intro r hr'
    have hne : r ≠ r0 := fun he ↦ h0 (he ▸ hr')
    simp [hne]

/-- The literal finite-window descending factorial is the finite surplus
sum of actual complete-excursion ordered tuple statistics. -/
theorem window_mixedStatistic_eq_statistic_sum (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)))
    (p : Path × (ℕ → ℕ)) (hg : Good lambda p.1) :
    ENNReal.ofReal (mixedStatistic m J S q
      (BrownianExcursionWindowPointMeasure.windowPointMeasure lambda m (pathInput p))) =
      ∑ r ∈ cellSurplusIndices m S q,
        statistic lambda (fun _ ↦ lower m) (fun _ ↦ upper m) r
          (fun z ↦ ENNReal.ofReal
            (cellWeight (fun j ↦ J (label q j)) (fun j ↦ (z j).1.val))) p := by
  let A : D → Set (SurplusWindow (lower m) (upper m) m) :=
    fun i ↦ windowEmbedding (lower m) (upper m) m ⁻¹' sizeSurplusCells J S i
  have hA : Pairwise (fun i j ↦ Disjoint (A i) (A j)) := fun _ _ hij ↦ (hdis hij).preimage _
  have hAm (i : D) : MeasurableSet (A i) :=
    (measurable_windowEmbedding _ _ _) (measurableSet_sizeSurplusCells J S hJ i)
  let B := selected lambda m (pathInput p)
  let t := (finite_selected lambda m (pathInput p)).toFinset
  let x := fun e ↦ windowAtom lambda m e (pathInput p)
  have ht : B = (t : Set ℚ) := by
    ext e
    exact (Set.Finite.mem_toFinset _).symm
  have hM : BrownianExcursionWindowPointMeasure.windowPointMeasure lambda m (pathInput p) =
      CountableFiniteAtomSampling.ofFinset t x :=
    CountableFiniteAtomSampling.pointMeasure_eq_ofFinset _ _ _ t ht
  change ENNReal.ofReal (factorialPolynomial q (fun i ↦ count _ (A i))) = _
  rw [hM]
  change ENNReal.ofReal (factorialPolynomial q
    (fun i ↦ count (FinitePointMeasureFintype.ofFintype (fun j : t ↦ x j.val)) (A i))) = _
  rw [factorialPolynomial_eq_tuple_card (fun i : t ↦ x i.val) A q hA hAm]
  simp only [ENNReal.ofReal_natCast]
  have hc : (Fintype.card (OrderedCellTuples (fun i : t ↦ x i.val) A q) : ℝ≥0∞) =
      ∑' e : Fin (∑ i, q i) → ℚ, if Function.Injective e ∧
        ∀ j, e j ∈ t ∧ x (e j) ∈ A (label q j) then (1 : ℝ≥0∞) else 0 := by
    rw [Fintype.card_eq_nat_card]
    have hraw := CountableFiniteTupleSampling.tsum_tuple_indicator_eq_card t x
      (fun j ↦ A (label q j))
    simp only [Fintype.card_eq_nat_card] at hraw
    convert hraw.symm using 1
    all_goals first | rfl | (apply tsum_congr; intro e; split_ifs <;> rfl)
  rw [hc]
  change _ = ∑ r ∈ cellSurplusIndices m S q, ∑' e : Fin (∑ i, q i) → ℚ,
    contribution lambda (fun _ ↦ lower m) (fun _ ↦ upper m) r (lengthCellTest J q) e p
  rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  apply tsum_congr
  intro e
  rw [contribution_sum]
  congr 1
  have hs (j) := selected_cell_iff lambda m J S p hg (label q j) (e j)
  simp only [t,Set.Finite.mem_toFinset]
  apply propext
  constructor
  · rintro ⟨hinj,hall⟩
    have hall' (j) := (hs j).mp (hall j)
    exact ⟨⟨hinj,fun j ↦ ⟨(hall' j).1,(hall' j).2.1⟩⟩,
      fun j ↦ (hall' j).2.2.1,fun j ↦ (hall' j).2.2.2⟩
  · rintro ⟨⟨hinj,hall⟩,hJ',hS'⟩
    exact ⟨hinj,fun j ↦ (hs j).mpr ⟨(hall j).1,(hall j).2,hJ' j,(hS' j).1,(hS' j).2⟩⟩

theorem ae_window_mixedStatistic_eq_statistic_sum (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    ∀ᵐ p ∂BrownianFullHorizonPoissonMarks.pathJointLaw lambda,
      ENNReal.ofReal (mixedStatistic m J S q
        (BrownianExcursionWindowPointMeasure.windowPointMeasure lambda m (pathInput p))) =
        ∑ r ∈ cellSurplusIndices m S q,
          statistic lambda (fun _ ↦ lower m) (fun _ ↦ upper m) r
            (fun z ↦ ENNReal.ofReal
              (cellWeight (fun j ↦ J (label q j)) (fun j ↦ (z j).1.val))) p := by
  have hg : ∀ᵐ p ∂BrownianFullHorizonPoissonMarks.pathJointLaw lambda, Good lambda p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [BrownianFullHorizonPoissonMarks.pathJointLaw_source]
    exact ae_good lambda
  exact hg.mono (fun p hp ↦ window_mixedStatistic_eq_statistic_sum lambda m J S q hJ hdis p hp)

end PerronWright.BrownianWindowCellTupleGeometry
