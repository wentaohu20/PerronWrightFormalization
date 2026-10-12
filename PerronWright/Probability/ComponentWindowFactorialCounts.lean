import PerronWright.Probability.ComponentWindowCounts
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Pi.Interval

/-!
# Actual ordered component tuples in integer and compact windows

The decomposition is a finite fibre-count identity for literal injective
component tuples. No point-process factorial moment identification is
assumed. Different coordinates may have different compact size cells.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ComponentWindowFactorialCounts

open ComponentCounts ComponentWindowPointMeasures FinitePointMeasureCompact

theorem card_mem_eq_sum_fibres {I J : Type*} [Fintype I] [DecidableEq J]
    (p : I → Prop) (f : I → J) (K : Finset J) :
    Fintype.card {t : I // p t ∧ f t ∈ K} =
      ∑ k ∈ K, Fintype.card {t : I // p t ∧ f t = k} := by
  classical
  simp only [Fintype.card_subtype]
  simpa only [Finset.filter_filter] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ.filter p) K f).symm

def sizes {n q : ℕ} {G : SimpleGraph (Fin n)} (t : Fin q ↪ G.ConnectedComponent) :
    Fin q → ℕ := fun i ↦ componentSize (t i)

def surpluses {n q : ℕ} {G : SimpleGraph (Fin n)} (t : Fin q ↪ G.ConnectedComponent) :
    Fin q → ℕ := fun i ↦ componentSurplus (t i)

theorem count_eq_fibre_card {n q : ℕ} (G : SimpleGraph (Fin n)) (k r : Fin q → ℕ) :
    ComponentCounts.count G k r =
      Fintype.card {t : Fin q ↪ G.ConnectedComponent // sizes t = k ∧ surpluses t = r} := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  simp only [sizes, surpluses, funext_iff, forall_and]

/-- Actual ordered distinct component tuples selected by an integer
size grid, with a prescribed surplus in each labelled coordinate. -/
def fixedSurplusCount {n q : ℕ} (G : SimpleGraph (Fin n))
    (K : Finset (Fin q → ℕ)) (r : Fin q → ℕ) : ℕ :=
  Fintype.card {t : Fin q ↪ G.ConnectedComponent // sizes t ∈ K ∧ surpluses t = r}

theorem fixedSurplusCount_eq_sum {n q : ℕ} (G : SimpleGraph (Fin n))
    (K : Finset (Fin q → ℕ)) (r : Fin q → ℕ) :
    fixedSurplusCount G K r = ∑ k ∈ K, ComponentCounts.count G k r := by
  unfold fixedSurplusCount
  have he : Fintype.card {t : Fin q ↪ G.ConnectedComponent //
      sizes t ∈ K ∧ surpluses t = r} =
      Fintype.card {t : Fin q ↪ G.ConnectedComponent //
        surpluses t = r ∧ sizes t ∈ K} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ ↦ and_comm))
  rw [he]
  have hfibre : Fintype.card {t : Fin q ↪ G.ConnectedComponent //
      surpluses t = r ∧ sizes t ∈ K} =
      ∑ k ∈ K, Fintype.card {t : Fin q ↪ G.ConnectedComponent //
        surpluses t = r ∧ sizes t = k} := by
    simpa only [Fintype.card_eq_nat_card] using
      card_mem_eq_sum_fibres (fun t : Fin q ↪ G.ConnectedComponent ↦ surpluses t = r)
        (sizes (G := G)) K
  rw [hfibre]
  apply Finset.sum_congr rfl
  intro k _
  rw [count_eq_fibre_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ ↦ and_comm))

def gridCount {n q : ℕ} (G : SimpleGraph (Fin n))
    (K L : Finset (Fin q → ℕ)) : ℕ :=
  Fintype.card {t : Fin q ↪ G.ConnectedComponent // sizes t ∈ K ∧ surpluses t ∈ L}

theorem gridCount_eq_sum_fixedSurplus {n q : ℕ} (G : SimpleGraph (Fin n))
    (K L : Finset (Fin q → ℕ)) :
    gridCount G K L = ∑ r ∈ L, fixedSurplusCount G K r := by
  simpa only [gridCount, fixedSurplusCount, Fintype.card_eq_nat_card] using
    card_mem_eq_sum_fibres (fun t : Fin q ↪ G.ConnectedComponent ↦ sizes t ∈ K)
      (surpluses (G := G)) L

theorem gridCount_eq_sum_counts {n q : ℕ} (G : SimpleGraph (Fin n))
    (K L : Finset (Fin q → ℕ)) :
    gridCount G K L = ∑ r ∈ L, ∑ k ∈ K, ComponentCounts.count G k r := by
  rw [gridCount_eq_sum_fixedSurplus]
  simp_rw [fixedSurplusCount_eq_sum]

/-- Literal integer tuple indices for independently chosen size cells. -/
def integerWindow {q : ℕ} (h : ℝ) (a b : Fin q → ℝ) : Finset (Fin q → ℕ) :=
  Finset.Icc (fun i ↦ ⌈a i * h⌉₊) (fun i ↦ ⌊b i * h⌋₊)

theorem mem_integerWindow {q : ℕ} {h : ℝ} (hh : 0 < h)
    (a b : Fin q → ℝ) (hb : ∀ i, 0 ≤ b i) {k : Fin q → ℕ} :
    k ∈ integerWindow h a b ↔ ∀ i, (k i : ℝ) / h ∈ Set.Icc (a i) (b i) := by
  simp only [integerWindow, Finset.mem_Icc, Pi.le_def, Nat.ceil_le]
  simp_rw [Nat.le_floor_iff (mul_nonneg (hb _) hh.le)]
  constructor
  · rintro ⟨ha, hb⟩ i
    exact ⟨(le_div_iff₀ hh).mpr (ha i), (div_le_iff₀ hh).mpr (hb i)⟩
  · intro hk
    exact ⟨fun i ↦ (le_div_iff₀ hh).mp (hk i).1,
      fun i ↦ (div_le_iff₀ hh).mp (hk i).2⟩

/-- Actual compact-cell tuple count, retaining injectivity of the
component tuple and the literal surplus of each component. -/
def compactFixedSurplusCount {n q : ℕ} (G : SimpleGraph (Fin n))
    (a b : Fin q → ℝ) (r : Fin q → ℕ) : ℕ :=
  Fintype.card {t : Fin q ↪ G.ConnectedComponent //
    (∀ i, (componentSize (t i) : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc (a i) (b i)) ∧
      surpluses t = r}

/-- Exact identity in different coordinate windows, at every positive
graph size. This is the bridge to literal integer factorial expectations. -/
theorem compactFixedSurplusCount_eq_sum {n q : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (a b : Fin q → ℝ) (hb : ∀ i, 0 ≤ b i) (r : Fin q → ℕ) :
    compactFixedSurplusCount G a b r =
      ∑ k ∈ integerWindow ((n : ℝ) ^ (2 / 3 : ℝ)) a b, ComponentCounts.count G k r := by
  have hh : 0 < (n : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  rw [← fixedSurplusCount_eq_sum]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  exact and_congr (mem_integerWindow hh a b hb).symm Iff.rfl

def surplusIndices (q R : ℕ) : Finset (Fin q → ℕ) :=
  Finset.Icc (fun _ ↦ 0) (fun _ ↦ R)

theorem mem_surplusIndices {q R : ℕ} {r : Fin q → ℕ} :
    r ∈ surplusIndices q R ↔ ∀ i, r i ≤ R := by
  simp [surplusIndices, Finset.mem_Icc, Pi.le_def]

/-- Forgetting the subtype certificates gives exactly the selected
injective genuine component tuples, and conversely packages every one. -/
def windowTupleEquiv {n q : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) :
    (Fin q ↪ WindowComponent a b R 1 G) ≃
      {t : Fin q ↪ G.ConnectedComponent // ∀ i, componentAtom 1 (t i) ∈ windowSet a b R} where
  toFun u := ⟨⟨fun i ↦ (u i).val, fun i j hij ↦ u.injective (Subtype.ext hij)⟩,
    fun i ↦ (u i).property⟩
  invFun t := ⟨fun i ↦ ⟨t.val i, t.property i⟩,
    fun i j hij ↦ t.val.injective (congrArg Subtype.val hij)⟩
  left_inv u := by
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv t := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl

theorem gridCount_eq_window_tuple_card {n q : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (a b : ℝ) (hb : 0 ≤ b) (R : ℕ) :
    gridCount G (integerWindow ((n : ℝ) ^ (2 / 3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b))
      (surplusIndices q R) = Fintype.card (Fin q ↪ WindowComponent a b R 1 G) := by
  have hh : 0 < (n : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  rw [Fintype.card_congr (windowTupleEquiv G a b R)]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  rw [mem_integerWindow hh _ _ (fun _ ↦ hb), mem_surplusIndices]
  simp only [sizes, surpluses, componentAtom, windowSet, one_mul, Set.mem_prod,
    Set.mem_Iic, forall_and]

/-- The actual mass falling factorial is exactly the sum of all
literal integer component tuple counts in the bounded-surplus window. -/
theorem window_size_descFactorial_eq_sum {n q : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (a b : ℝ) (hb : 0 ≤ b) (R : ℕ) :
    (size (windowPointMeasure a b R 1 G)).descFactorial q =
      ∑ r ∈ surplusIndices q R,
        ∑ k ∈ integerWindow ((n : ℝ) ^ (2 / 3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b),
          ComponentCounts.count G k r := by
  rw [← gridCount_eq_sum_counts, gridCount_eq_window_tuple_card G hn a b hb R,
    Fintype.card_embedding_eq, Fintype.card_fin, windowPointMeasure_size]

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

theorem fixedSurplusCount_expectation_eq_sum (M : CompactBJRModel S)
    (lambda : ℝ) (n q : ℕ) (K : Finset (Fin q → ℕ)) (r : Fin q → ℕ) :
    (∫ G, (fixedSurplusCount G K r : ℝ) ∂AnnealedGraph.law M
      (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) =
      ∑ k ∈ K, (∫ G, (ComponentCounts.count G k r : ℝ) ∂AnnealedGraph.law M
        (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) := by
  simp_rw [fixedSurplusCount_eq_sum, Nat.cast_sum]
  exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)

theorem compactFixedSurplusCount_expectation_eq_sum (M : CompactBJRModel S)
    (lambda : ℝ) (n q : ℕ) (hn : 0 < n) (a b : Fin q → ℝ)
    (hb : ∀ i, 0 ≤ b i) (r : Fin q → ℕ) :
    (∫ G, (compactFixedSurplusCount G a b r : ℝ) ∂AnnealedGraph.law M
      (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) =
      ∑ k ∈ integerWindow ((n : ℝ) ^ (2 / 3 : ℝ)) a b,
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂AnnealedGraph.law M
          (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) := by
  simp_rw [compactFixedSurplusCount_eq_sum _ hn a b hb, Nat.cast_sum]
  exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)

/-- This observable is measurable on the actual weak-Borel point space,
and integrable under each actual window law. -/
theorem windowLaw_descFactorial_integrable (M : CompactBJRModel S)
    (lambda a b : ℝ) (R n q : ℕ) :
    Integrable (fun η ↦ ((size η).descFactorial q : ℝ))
      (unmarkedWindowLaw M lambda a b R n : Measure (PointMeasure (SurplusWindow a b R))) :=
  windowLaw_integrable M lambda a b R 1 n
    ((measurable_of_countable (fun m : ℕ ↦ (m.descFactorial q : ℝ))).comp measurable_size)

theorem windowLaw_descFactorial_expectation_eq_sum (M : CompactBJRModel S)
    (lambda a b : ℝ) (hb : 0 ≤ b) (R n q : ℕ) (hn : 0 < n) :
    (∫ η, ((size η).descFactorial q : ℝ) ∂(unmarkedWindowLaw M lambda a b R n :
      Measure (PointMeasure (SurplusWindow a b R)))) =
      ∑ r ∈ surplusIndices q R,
        ∑ k ∈ integerWindow ((n : ℝ) ^ (2 / 3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b),
          (∫ G, (ComponentCounts.count G k r : ℝ) ∂AnnealedGraph.law M
            (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) := by
  have hm : Measurable (fun η : PointMeasure (SurplusWindow a b R) ↦
      ((size η).descFactorial q : ℝ)) :=
    (measurable_of_countable (fun m : ℕ ↦ (m.descFactorial q : ℝ))).comp measurable_size
  unfold unmarkedWindowLaw
  rw [windowLaw_integral M lambda a b R 1 n hm]
  simp_rw [window_size_descFactorial_eq_sum _ hn a b hb R, Nat.cast_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)
  · intro _ _
    exact Integrable.of_finite

end PerronWright.ComponentWindowFactorialCounts
