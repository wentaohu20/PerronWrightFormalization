import PerronWright.Probability.BrownianActualWindowCellMoments
import PerronWright.Probability.BrownianArbitraryWindowLaw

/-! # Genuine cell moments in arbitrary Brownian closed windows

The measurable restriction of a sufficiently large canonical chart is
used literally, including its boundary atoms. Clipping spatial cells and
the finite surplus grid reduces the actual count moments to the already
proved canonical moments; clipping the same density integral gives the
stated arbitrary-window formula. No restriction-continuity, boundary
nullity, or factorial-moment identity is an input.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianActualArbitraryWindowCellMoments

open ComponentGlobalPointProcess ComponentWindowPointMeasures ComponentWindowMixedFactorials
open PositiveSizeSurplusExhaustion GlobalPointMeasureCharts FinitePointMeasureCompact
open FinitePointMeasureMixedFactorials FactorialCountDeterminacy
open SizeCellIndicators CompactSizeCellFactorialLimits CompactSizeCellMomentBounds FactorialDensity

variable {D : Type*} [Fintype D]

def mixedStatistic (a b : ℝ) (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (q : D → ℕ) (η : PointMeasure (SurplusWindow a b R)) : ℝ :=
  factorialPolynomial q (fun i ↦ count η (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i))

theorem measurable_mixedStatistic (a b : ℝ) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) : Measurable (mixedStatistic a b R J S q) :=
  measurable_window_mixed_factorial a b R _ q
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))

private theorem statistic_nonneg (a b : ℝ) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (η : PointMeasure (SurplusWindow a b R)) : 0 ≤ mixedStatistic a b R J S q η :=
  Finset.prod_nonneg (fun _ _ ↦ Nat.cast_nonneg _)

private theorem restriction_counts (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (m : ℕ) (η : Chart m) (J : Set ℝ) (S : Finset ℕ) (hJ : MeasurableSet J) :
    count (BrownianArbitraryWindowLaw.chartRestriction a b R ha m η)
      (windowEmbedding a b R ⁻¹' (J ×ˢ (S : Set ℕ))) =
      count η (windowEmbedding (lower m) (upper m) m ⁻¹'
        ((J ∩ Icc a b) ×ˢ ((S.filter (fun r ↦ r ≤ R)) : Set ℕ))) := by
  have hA : MeasurableSet (windowEmbedding a b R ⁻¹' (J ×ˢ (S : Set ℕ))) :=
    (measurable_windowEmbedding a b R) (hJ.prod S.measurableSet)
  have he : positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) ⁻¹'
      (positiveWindowEmbedding a b R ha ''
        (windowEmbedding a b R ⁻¹' (J ×ˢ (S : Set ℕ)))) =
      windowEmbedding (lower m) (upper m) m ⁻¹'
        ((J ∩ Icc a b) ×ˢ ((S.filter (fun r ↦ r ≤ R)) : Set ℕ)) := by
    ext z
    constructor
    · rintro ⟨y,hy,hyz⟩
      have hx : y.1.val = z.1.val := congrArg (fun v : PositiveSizeSurplus ↦ v.1.val) hyz
      have hr : y.2.val = z.2.val := congrArg (fun v : PositiveSizeSurplus ↦ v.2) hyz
      change z.1.val ∈ J ∩ Icc a b ∧ z.2.val ∈ S.filter (fun r ↦ r ≤ R)
      change y.1.val ∈ J ∧ y.2.val ∈ S at hy
      refine ⟨⟨hx ▸ hy.1,hx ▸ y.1.property⟩,Finset.mem_filter.mpr ⟨hr ▸ hy.2,?_⟩⟩
      exact hr ▸ Nat.le_of_lt_succ y.2.isLt
    · intro hz
      change z.1.val ∈ J ∩ Icc a b ∧ z.2.val ∈ S.filter (fun r ↦ r ≤ R) at hz
      have hs := Finset.mem_filter.mp hz.2
      let y : SurplusWindow a b R := (⟨z.1.val,hz.1.2⟩,⟨z.2.val,Nat.lt_succ_iff.mpr hs.2⟩)
      refine ⟨y,⟨hz.1.1,hs.1⟩,?_⟩
      rfl
  unfold count
  apply congrArg (fun x : ℝ≥0∞ ↦ ⌊x.toReal⌋₊)
  rw [BrownianArbitraryWindowLaw.chartRestriction_apply a b R ha m η hA,he]

private theorem clipped_cellMomentMass (lambda a b L U : ℝ) (R M : ℕ)
    (hL : L ≤ a) (hU : b ≤ U) (hRM : R ≤ M)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ) :
    cellMomentMass 1 1 lambda L U M (fun i ↦ J i ∩ Icc a b)
      (fun i ↦ (S i).filter (fun r ↦ r ≤ R)) q =
      cellMomentMass 1 1 lambda a b R J S q := by
  have hs : cellSurplusIndices M (fun i ↦ (S i).filter (fun r ↦ r ≤ R)) q =
      cellSurplusIndices R S q := by
    ext r
    rw [mem_cellSurplusIndices,mem_cellSurplusIndices]
    simp only [Finset.mem_filter]
    constructor
    · intro hr j
      exact ⟨(hr j).2.2,(hr j).2.1⟩
    · intro hr j
      exact ⟨(hr j).1.trans hRM,(hr j).2,(hr j).1⟩
  unfold cellMomentMass
  rw [hs]
  apply Finset.sum_congr rfl
  intro r _
  have hw (x : Fin (∑ i, q i) → ℝ) :
      cellWeight (fun j ↦ J (label q j) ∩ Icc a b) x * density 1 1 lambda x r =
      (sizeWindow (∑ i, q i) a b).indicator
        (fun x ↦ cellWeight (fun j ↦ J (label q j)) x * density 1 1 lambda x r) x := by
    by_cases hx : x ∈ sizeWindow (∑ i, q i) a b
    · have hb := mem_sizeWindow.mp hx
      rw [indicator_of_mem hx]
      simp only [cellWeight_eq,Set.mem_inter_iff]
      have hh : (∀ j, x j ∈ J (label q j) ∧ x j ∈ Icc a b) ↔
          ∀ j, x j ∈ J (label q j) :=
        ⟨fun h j ↦ (h j).1,fun h j ↦ ⟨h j,hb j⟩⟩
      simp only [hh]
    · have hn : ¬∀ j, x j ∈ J (label q j) ∩ Icc a b :=
        fun h ↦ hx (mem_sizeWindow.mpr (fun j ↦ (h j).2))
      rw [indicator_of_notMem hx,cellWeight_eq,if_neg hn,zero_mul]
  simp_rw [hw]
  have hB : MeasurableSet (sizeWindow (∑ i, q i) a b) := measurableSet_Icc
  have hi : sizeWindow (∑ i, q i) L U ∩ sizeWindow (∑ i, q i) a b =
      sizeWindow (∑ i, q i) a b := by
    apply inter_eq_right.mpr
    intro x hx
    exact mem_sizeWindow.mpr (fun j ↦
      ⟨hL.trans ((mem_sizeWindow.mp hx) j).1,((mem_sizeWindow.mp hx) j).2.trans hU⟩)
  rw [setIntegral_indicator hB,hi]

theorem windowLaw_mixed_factorial_lintegral (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫⁻ η, ENNReal.ofReal (mixedStatistic a b R J S q η)
      ∂(BrownianArbitraryWindowLaw.law lambda a b R ha hab : Measure _)) =
      ENNReal.ofReal (cellMomentMass 1 1 lambda a b R J S q) := by
  obtain ⟨m,hsub⟩ := exists_compact_subset_window (isCompact_positiveWindowSet a b R ha)
  have hleft := hsub (show (⟨a,ha⟩,0) ∈ positiveWindowSet a b R from
    ⟨⟨le_rfl,hab⟩,Nat.zero_le R⟩)
  have hright := hsub (show (⟨b,ha.trans_le hab⟩,R) ∈ positiveWindowSet a b R from by
    change b ∈ Icc a b ∧ R ≤ R
    exact ⟨⟨hab,le_rfl⟩,le_rfl⟩)
  have hL : lower m ≤ a := hleft.1.1
  have hU : b ≤ upper m := hright.1.2
  have hRM : R ≤ m := hright.2
  let J' := fun i ↦ J i ∩ Icc a b
  let S' := fun i ↦ (S i).filter (fun r ↦ r ≤ R)
  have hJ' (i : D) : MeasurableSet (J' i) := (hJ i).inter measurableSet_Icc
  have hdis' : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J' S' i) (sizeSurplusCells J' S' j)) := by
    intro i j hij
    apply (hdis hij).mono
    · exact fun _ hz ↦ ⟨hz.1.1,(Finset.mem_filter.mp hz.2).1⟩
    · exact fun _ hz ↦ ⟨hz.1.1,(Finset.mem_filter.mp hz.2).1⟩
  have he (η : Chart m) :
      mixedStatistic a b R J S q (BrownianArbitraryWindowLaw.chartRestriction a b R ha m η) =
      BrownianWindowCellTupleGeometry.mixedStatistic m J' S' q η := by
    apply Finset.prod_congr rfl
    intro i _
    dsimp [J',S',sizeSurplusCells]
    rw [restriction_counts a b R ha m η (J i) (S i) (hJ i)]
  rw [BrownianArbitraryWindowLaw.law_eq_chart_map lambda a b R ha hab m hsub,
    ProbabilityMeasure.toMeasure_map,
    lintegral_map (measurable_mixedStatistic a b R J S q hJ).ennreal_ofReal
      (BrownianArbitraryWindowLaw.measurable_chartRestriction a b R ha hab m)]
  simp_rw [he]
  rw [BrownianActualWindowCellMoments.windowLaw_mixed_factorial_lintegral lambda m J' S' q hJ' hdis',
    clipped_cellMomentMass lambda a b _ _ R m hL hU hRM J S q]

theorem windowLaw_mixed_factorial_integrable (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    Integrable (mixedStatistic a b R J S q)
      (BrownianArbitraryWindowLaw.law lambda a b R ha hab : Measure _) := by
  refine ⟨(measurable_mixedStatistic a b R J S q hJ).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (statistic_nonneg a b R J S q)),
    windowLaw_mixed_factorial_lintegral lambda a b R ha hab J S q hJ hdis]
  exact ENNReal.ofReal_lt_top

theorem windowLaw_mixed_factorial_integral (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫ η, mixedStatistic a b R J S q η
      ∂(BrownianArbitraryWindowLaw.law lambda a b R ha hab : Measure _)) =
      cellMomentMass 1 1 lambda a b R J S q := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (statistic_nonneg a b R J S q))
    (cellMomentMass_nonneg 1 lambda a b (by norm_num) ha R J S q)).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    (windowLaw_mixed_factorial_integrable lambda a b R ha hab J S q hJ hdis)
    (Eventually.of_forall (statistic_nonneg a b R J S q))]
  exact windowLaw_mixed_factorial_lintegral lambda a b R ha hab J S q hJ hdis

def cellCountLaw (lambda a b : ℝ) (R : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    ProbabilityMeasure (D → ℕ) :=
  FinitePointMeasureMeasurable.countLaw (BrownianArbitraryWindowLaw.law lambda a b R ha hab)
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))

theorem all_mixed_factorial_moments (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∀ q, Integrable (factorialPolynomial q)
      (cellCountLaw lambda a b R ha hab J S hJ : Measure (D → ℕ))) ∧
    (∀ q, factorialMoment (cellCountLaw lambda a b R ha hab J S hJ : Measure (D → ℕ)) q =
      cellMomentMass 1 1 lambda a b R J S q) := by
  have hm := FinitePointMeasureMeasurable.measurable_count_vector
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))
  constructor
  · intro q
    change Integrable (factorialPolynomial q)
      ((BrownianArbitraryWindowLaw.law lambda a b R ha hab :
        Measure (PointMeasure (SurplusWindow a b R))).map _)
    exact (integrable_map_measure
      (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable hm.aemeasurable).mpr
      (windowLaw_mixed_factorial_integrable lambda a b R ha hab J S q hJ hdis)
  · intro q
    change (∫ n, factorialPolynomial q n
      ∂(BrownianArbitraryWindowLaw.law lambda a b R ha hab :
        Measure (PointMeasure (SurplusWindow a b R))).map _) = _
    rw [integral_map hm.aemeasurable
      (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
    exact windowLaw_mixed_factorial_integral lambda a b R ha hab J S q hJ hdis

theorem summable_actual_cell_factorial_moments (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    Summable (fun q : D → ℕ ↦ (2 : ℝ)^(∑ i, q i) *
      factorialMoment (cellCountLaw lambda a b R ha hab J S hJ : Measure (D → ℕ)) q /
        ∏ i, ((q i).factorial : ℝ)) := by
  simp_rw [(all_mixed_factorial_moments lambda a b R ha hab J S hJ hdis).2]
  exact summable_cellMomentMass_factorial 1 lambda (by norm_num) ha hab R J S hJ

end PerronWright.BrownianActualArbitraryWindowCellMoments
