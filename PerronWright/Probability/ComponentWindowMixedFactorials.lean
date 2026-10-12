import PerronWright.Probability.FinitePointMeasureMixedFactorials
import PerronWright.Probability.ComponentWindowFactorialCounts

/-!
# Actual mixed cell-count factorial moments of graph window laws

Arbitrary disjoint Borel cells have a literal component-tuple cardinal
identity. Rectangular size-surplus cells then give exactly the integer
`ComponentCounts.count` sums, under the existing genuine graph law.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ComponentWindowMixedFactorials

open ComponentCounts ComponentWindowPointMeasures ComponentWindowFactorialCounts
open FinitePointMeasureCompact FinitePointMeasureMixedFactorials FactorialCountDeterminacy

variable {D : Type*} [Fintype D]

theorem window_mixed_factorial_eq_card (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) (A : D → Set (SurplusWindow a b R)) (q : D → ℕ)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hAm : ∀ i, MeasurableSet (A i)) :
    factorialPolynomial q (fun i ↦ count (windowPointMeasure a b R c G) (A i)) =
      (Fintype.card (OrderedCellTuples (windowAtom a b R c (G := G)) A q) : ℝ) :=
  factorialPolynomial_eq_tuple_card _ A q hA hAm

theorem measurable_window_mixed_factorial (a b : ℝ) (R : ℕ)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ)
    (hAm : ∀ i, MeasurableSet (A i)) :
    Measurable (fun η : PointMeasure (SurplusWindow a b R) ↦
      factorialPolynomial q (fun i ↦ count η (A i))) :=
  (measurable_of_countable (factorialPolynomial q)).comp
    (FinitePointMeasureMeasurable.measurable_count_vector A hAm)

def AmbientWindowTuples (a b : ℝ) (R : ℕ) (c : ℝ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (B : D → Set (ℝ × ℕ)) (q : D → ℕ) :=
  {t : Fin (∑ i, q i) ↪ G.ConnectedComponent // ∀ j,
    componentAtom c (t j) ∈ windowSet a b R ∧
      componentAtom c (t j) ∈ B (label q j)}

instance (a b : ℝ) (R : ℕ) (c : ℝ) {n : ℕ} (G : SimpleGraph (Fin n))
    (B : D → Set (ℝ × ℕ)) (q : D → ℕ) : Fintype (AmbientWindowTuples a b R c G B q) :=
  inferInstanceAs (Fintype {t : Fin (∑ i, q i) ↪ G.ConnectedComponent // ∀ j,
    componentAtom c (t j) ∈ windowSet a b R ∧ componentAtom c (t j) ∈ B (label q j)})

def ambientCellTupleEquiv (a b : ℝ) (R : ℕ) (c : ℝ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (B : D → Set (ℝ × ℕ)) (q : D → ℕ) :
    OrderedCellTuples (windowAtom a b R c (G := G))
      (fun i ↦ windowEmbedding a b R ⁻¹' B i) q ≃ AmbientWindowTuples a b R c G B q where
  toFun e := ⟨⟨fun j ↦ (e.val j).val,
    fun i j hij ↦ e.val.injective (Subtype.ext hij)⟩, by
    intro j
    change componentAtom c (e.val j).val ∈ windowSet a b R ∧
      componentAtom c (e.val j).val ∈ B (label q j)
    refine ⟨(e.val j).property, ?_⟩
    have hj := e.property j
    change windowEmbedding a b R (windowAtom a b R c (e.val j)) ∈ B (label q j) at hj
    simpa only [windowEmbedding_windowAtom] using hj⟩
  invFun t := ⟨⟨fun j ↦ ⟨t.val j, (t.property j).1⟩,
    fun i j hij ↦ t.val.injective (congrArg Subtype.val hij)⟩, by
    intro j
    change componentAtom c (t.val j) ∈ B (label q j)
    exact (t.property j).2⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro j
    rfl
  right_inv t := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro j
    rfl

def rectangleCells (lo hi : D → ℝ) (S : D → Finset ℕ) (i : D) : Set (ℝ × ℕ) :=
  Set.Icc (lo i) (hi i) ×ˢ (S i : Set ℕ)

omit [Fintype D] in
theorem measurableSet_rectangleCells (lo hi : D → ℝ) (S : D → Finset ℕ) (i : D) :
    MeasurableSet (rectangleCells lo hi S i) :=
  measurableSet_Icc.prod (S i).measurableSet

def rectangleSizeIndices (n : ℕ) (lo hi : D → ℝ) (q : D → ℕ) :
    Finset (Fin (∑ i, q i) → ℕ) :=
  integerWindow ((n : ℝ) ^ (2 / 3 : ℝ)) (fun j ↦ lo (label q j)) (fun j ↦ hi (label q j))

def rectangleSurplusIndices (S : D → Finset ℕ) (q : D → ℕ) :
    Finset (Fin (∑ i, q i) → ℕ) := Fintype.piFinset (fun j ↦ S (label q j))

/-- Rectangular tuple membership is exactly membership of its literal
integer size and surplus vectors in the corresponding finite grids. -/
theorem ambient_rectangle_tuple_card_eq_grid {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (a b : ℝ) (R : ℕ) (lo hi : D → ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hhi : ∀ i, 0 ≤ hi i)
    (hsub : ∀ i, rectangleCells lo hi S i ⊆ windowSet a b R) :
    Fintype.card (AmbientWindowTuples a b R 1 G (rectangleCells lo hi S) q) =
      gridCount G (rectangleSizeIndices n lo hi q) (rectangleSurplusIndices S q) := by
  have hd : 0 < (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  unfold rectangleSizeIndices rectangleSurplusIndices
  rw [mem_integerWindow hd _ _ (fun j ↦ hhi (label q j)), Fintype.mem_piFinset]
  have hm (j) : componentAtom 1 (t j) ∈ rectangleCells lo hi S (label q j) ↔
      (componentSize (t j) : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈
        Set.Icc (lo (label q j)) (hi (label q j)) ∧ componentSurplus (t j) ∈ S (label q j) := by
    simp only [componentAtom, one_mul, rectangleCells, Set.mem_prod, Finset.mem_coe]
  constructor
  · intro ht
    exact ⟨fun j ↦ (hm j).mp (ht j).2 |>.1, fun j ↦ (hm j).mp (ht j).2 |>.2⟩
  · rintro ⟨hk, hr⟩ j
    have hb := (hm j).mpr ⟨hk j, hr j⟩
    exact ⟨hsub (label q j) hb, hb⟩

theorem window_rectangle_mixed_factorial_eq_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (a b : ℝ) (R : ℕ) (lo hi : D → ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hhi : ∀ i, 0 ≤ hi i)
    (hsub : ∀ i, rectangleCells lo hi S i ⊆ windowSet a b R)
    (hdis : Pairwise (fun i j ↦ Disjoint (rectangleCells lo hi S i) (rectangleCells lo hi S j))) :
    factorialPolynomial q (fun i ↦ count (windowPointMeasure a b R 1 G)
      (windowEmbedding a b R ⁻¹' rectangleCells lo hi S i)) =
      ∑ r ∈ rectangleSurplusIndices S q, ∑ k ∈ rectangleSizeIndices n lo hi q,
        (ComponentCounts.count G k r : ℝ) := by
  have hpre : Pairwise (fun i j ↦ Disjoint
      (windowEmbedding a b R ⁻¹' rectangleCells lo hi S i)
      (windowEmbedding a b R ⁻¹' rectangleCells lo hi S j)) := by
    intro i j hij
    exact (hdis hij).preimage _
  rw [window_mixed_factorial_eq_card a b R 1 G _ q hpre
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_rectangleCells lo hi S i)),
    Fintype.card_congr (ambientCellTupleEquiv a b R 1 G (rectangleCells lo hi S) q),
    ambient_rectangle_tuple_card_eq_grid G hn a b R lo hi S q hhi hsub,
    gridCount_eq_sum_counts]
  simp only [Nat.cast_sum]

/-- Borel size cells may be half-open, singleton, or arbitrary Borel
sets. The surplus cell is literally finite, as in a bounded window. -/
def sizeSurplusCells (J : D → Set ℝ) (S : D → Finset ℕ) (i : D) : Set (ℝ × ℕ) :=
  J i ×ˢ (S i : Set ℕ)

omit [Fintype D] in
theorem measurableSet_sizeSurplusCells (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (i : D) : MeasurableSet (sizeSurplusCells J S i) :=
  (hJ i).prod (S i).measurableSet

def cellSizeIndices (n : ℕ) (a b : ℝ) (J : D → Set ℝ) (q : D → ℕ) :
    Finset (Fin (∑ i, q i) → ℕ) :=
  (integerWindow ((n : ℝ) ^ (2 / 3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b)).filter
    (fun k ↦ ∀ j, (k j : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ J (label q j))

def cellSurplusIndices (R : ℕ) (S : D → Finset ℕ) (q : D → ℕ) :
    Finset (Fin (∑ i, q i) → ℕ) :=
  Fintype.piFinset (fun j ↦ (S (label q j)).filter (fun r ↦ r ≤ R))

theorem mem_cellSizeIndices {n : ℕ} (hn : 0 < n) (a b : ℝ) (hb : 0 ≤ b)
    (J : D → Set ℝ) (q : D → ℕ) (k : Fin (∑ i, q i) → ℕ) :
    k ∈ cellSizeIndices n a b J q ↔ ∀ j,
      (k j : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b ∧
        (k j : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ J (label q j) := by
  rw [cellSizeIndices, Finset.mem_filter,
    mem_integerWindow (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) _ _ (fun _ ↦ hb)]
  exact forall_and.symm

theorem mem_cellSurplusIndices (R : ℕ) (S : D → Finset ℕ) (q : D → ℕ)
    (r : Fin (∑ i, q i) → ℕ) :
    r ∈ cellSurplusIndices R S q ↔ ∀ j, r j ≤ R ∧ r j ∈ S (label q j) := by
  simp only [cellSurplusIndices, Fintype.mem_piFinset, Finset.mem_filter, and_comm]

theorem ambient_sizeSurplus_tuple_card_eq_grid {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (a b : ℝ) (hb : 0 ≤ b) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ) :
    Fintype.card (AmbientWindowTuples a b R 1 G (sizeSurplusCells J S) q) =
      gridCount G (cellSizeIndices n a b J q) (cellSurplusIndices R S q) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  rw [mem_cellSizeIndices hn a b hb, mem_cellSurplusIndices]
  simp only [componentAtom, windowSet, one_mul, Set.mem_prod, Set.mem_Iic,
    sizeSurplusCells, Finset.mem_coe, sizes, surpluses]
  constructor
  · intro ht
    exact ⟨fun j ↦ ⟨(ht j).1.1, (ht j).2.1⟩, fun j ↦ ⟨(ht j).1.2, (ht j).2.2⟩⟩
  · rintro ⟨hk, hr⟩ j
    exact ⟨⟨(hk j).1, (hr j).1⟩, ⟨(hk j).2, (hr j).2⟩⟩

/-- Exact mixed factorial decomposition for arbitrary disjoint Borel
size cells and finite surplus cells, including genuine half-open
partitions and boundary singleton cells. -/
theorem window_sizeSurplus_mixed_factorial_eq_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (a b : ℝ) (hb : 0 ≤ b) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    factorialPolynomial q (fun i ↦ count (windowPointMeasure a b R 1 G)
      (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)) =
      ∑ r ∈ cellSurplusIndices R S q, ∑ k ∈ cellSizeIndices n a b J q,
        (ComponentCounts.count G k r : ℝ) := by
  have hpre : Pairwise (fun i j ↦ Disjoint
      (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (windowEmbedding a b R ⁻¹' sizeSurplusCells J S j)) := by
    intro i j hij
    exact (hdis hij).preimage _
  rw [window_mixed_factorial_eq_card a b R 1 G _ q hpre
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i)),
    Fintype.card_congr (ambientCellTupleEquiv a b R 1 G (sizeSurplusCells J S) q),
    ambient_sizeSurplus_tuple_card_eq_grid G hn a b hb R J S q,
    gridCount_eq_sum_counts]
  simp only [Nat.cast_sum]

variable {T : Type*} [MetricSpace T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]

theorem windowLaw_mixed_factorial_integrable (M : CompactBJRModel T)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ) (hAm : ∀ i, MeasurableSet (A i)) :
    Integrable (fun η ↦ factorialPolynomial q (fun i ↦ count η (A i)))
      (windowLaw M lambda a b R c n : Measure (PointMeasure (SurplusWindow a b R))) :=
  windowLaw_integrable M lambda a b R c n (measurable_window_mixed_factorial a b R A q hAm)

theorem windowLaw_mixed_factorial_expectation_eq_card (M : CompactBJRModel T)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) (hAm : ∀ i, MeasurableSet (A i)) :
    (∫ η, factorialPolynomial q (fun i ↦ count η (A i))
      ∂(windowLaw M lambda a b R c n : Measure (PointMeasure (SurplusWindow a b R)))) =
      ∫ G, (Fintype.card (OrderedCellTuples (windowAtom a b R c (G := G)) A q) : ℝ)
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n := by
  have hm := measurable_window_mixed_factorial a b R A q hAm
  rw [windowLaw_integral M lambda a b R c n hm]
  simp_rw [window_mixed_factorial_eq_card a b R c _ A q hA hAm]

/-- The actual count-vector pushforward law has these same genuine
component-tuple mixed factorial moments. -/
theorem windowCountLaw_mixed_integral_eq_card (M : CompactBJRModel T)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) (hAm : ∀ i, MeasurableSet (A i)) :
    (∫ y, factorialPolynomial q y ∂(FinitePointMeasureMeasurable.countLaw
      (windowLaw M lambda a b R c n) A hAm : Measure (D → ℕ))) =
      ∫ G, (Fintype.card (OrderedCellTuples (windowAtom a b R c (G := G)) A q) : ℝ)
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n := by
  rw [FinitePointMeasureMeasurable.countLaw_toMeasure,
    integral_map (FinitePointMeasureMeasurable.measurable_count_vector A hAm).aemeasurable
      (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
  exact windowLaw_mixed_factorial_expectation_eq_card M lambda a b R c n A q hA hAm

theorem windowCountLaw_mixed_factorial_integrable (M : CompactBJRModel T)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ) (hAm : ∀ i, MeasurableSet (A i)) :
    Integrable (factorialPolynomial q) (FinitePointMeasureMeasurable.countLaw
      (windowLaw M lambda a b R c n) A hAm : Measure (D → ℕ)) := by
  rw [FinitePointMeasureMeasurable.countLaw_toMeasure]
  exact (integrable_map_measure (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable
    (FinitePointMeasureMeasurable.measurable_count_vector A hAm).aemeasurable).mpr
      (windowLaw_mixed_factorial_integrable M lambda a b R c n A q hAm)

theorem windowLaw_rectangle_mixed_factorial_expectation_eq_sum (M : CompactBJRModel T)
    (lambda a b : ℝ) (R n : ℕ) (hn : 0 < n)
    (lo hi : D → ℝ) (S : D → Finset ℕ) (q : D → ℕ) (hhi : ∀ i, 0 ≤ hi i)
    (hsub : ∀ i, rectangleCells lo hi S i ⊆ windowSet a b R)
    (hdis : Pairwise (fun i j ↦ Disjoint (rectangleCells lo hi S i) (rectangleCells lo hi S j))) :
    (∫ η, factorialPolynomial q (fun i ↦ count η
      (windowEmbedding a b R ⁻¹' rectangleCells lo hi S i))
      ∂(unmarkedWindowLaw M lambda a b R n : Measure (PointMeasure (SurplusWindow a b R)))) =
      ∑ r ∈ rectangleSurplusIndices S q, ∑ k ∈ rectangleSizeIndices n lo hi q,
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂AnnealedGraph.law M
          (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) := by
  have hm := measurable_window_mixed_factorial a b R
    (fun i ↦ windowEmbedding a b R ⁻¹' rectangleCells lo hi S i) q
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_rectangleCells lo hi S i))
  unfold unmarkedWindowLaw
  rw [windowLaw_integral M lambda a b R 1 n hm]
  simp_rw [window_rectangle_mixed_factorial_eq_sum _ hn a b R lo hi S q hhi hsub hdis]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)
  · intro _ _
    exact Integrable.of_finite

theorem windowLaw_sizeSurplus_mixed_factorial_expectation_eq_sum (M : CompactBJRModel T)
    (lambda a b : ℝ) (hb : 0 ≤ b) (R n : ℕ) (hn : 0 < n)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫ η, factorialPolynomial q (fun i ↦ count η
      (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i))
      ∂(unmarkedWindowLaw M lambda a b R n : Measure (PointMeasure (SurplusWindow a b R)))) =
      ∑ r ∈ cellSurplusIndices R S q, ∑ k ∈ cellSizeIndices n a b J q,
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂AnnealedGraph.law M
          (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) := by
  have hm := measurable_window_mixed_factorial a b R
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i) q
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))
  unfold unmarkedWindowLaw
  rw [windowLaw_integral M lambda a b R 1 n hm]
  simp_rw [window_sizeSurplus_mixed_factorial_eq_sum _ hn a b hb R J S q hJ hdis]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)
  · intro _ _
    exact Integrable.of_finite

/-- The genuine finite-dimensional count law of these actual window
cells. Its source is the already constructed annealed window law. -/
def sizeSurplusCountLaw (M : CompactBJRModel T) (lambda a b : ℝ) (R n : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    ProbabilityMeasure (D → ℕ) :=
  FinitePointMeasureMeasurable.countLaw (unmarkedWindowLaw M lambda a b R n)
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))

theorem sizeSurplusCountLaw_mixed_factorial_integrable (M : CompactBJRModel T)
    (lambda a b : ℝ) (R n : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (q : D → ℕ) :
    Integrable (factorialPolynomial q) (sizeSurplusCountLaw M lambda a b R n J S hJ :
      Measure (D → ℕ)) :=
  windowCountLaw_mixed_factorial_integrable M lambda a b R 1 n _ q
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))

/-- The complete actual finite-dimensional mixed count-law moment
identity, with no mixed-moment identification premise. -/
theorem sizeSurplusCountLaw_mixed_factorial_integral_eq_sum (M : CompactBJRModel T)
    (lambda a b : ℝ) (hb : 0 ≤ b) (R n : ℕ) (hn : 0 < n)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) (q : D → ℕ)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫ y, factorialPolynomial q y ∂(sizeSurplusCountLaw M lambda a b R n J S hJ :
      Measure (D → ℕ))) =
      ∑ r ∈ cellSurplusIndices R S q, ∑ k ∈ cellSizeIndices n a b J q,
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂AnnealedGraph.law M
          (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) := by
  unfold sizeSurplusCountLaw
  rw [FinitePointMeasureMeasurable.countLaw_toMeasure,
    integral_map (FinitePointMeasureMeasurable.measurable_count_vector _
      (fun i ↦ (measurable_windowEmbedding a b R)
        (measurableSet_sizeSurplusCells J S hJ i))).aemeasurable
      (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
  exact windowLaw_sizeSurplus_mixed_factorial_expectation_eq_sum M lambda a b hb R n hn
    J S q hJ hdis

end PerronWright.ComponentWindowMixedFactorials
