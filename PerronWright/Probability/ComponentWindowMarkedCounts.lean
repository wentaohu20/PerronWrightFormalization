import PerronWright.Probability.AnnealedMarkedFactorialExchangeability
import PerronWright.Probability.ComponentWindowFactorialCounts

/-! # Literal marked sums over actual compact-window component tuples

All marks belong to actual connected components of the sampled typed
graph. Integer size/surplus partitioning is a proved finite fibre sum.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Real Classical Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.ComponentWindowMarkedCounts

open ComponentWindowFactorialCounts ComponentWindowPointMeasures ComponentCounts
  AnnealedMarkedFactorialCounting AnnealedMarkedFactorialExchangeability EmpiricalTypeMarks AnnealedGraph

theorem sum_mem_eq_sum_fibres {I J : Type*} [Fintype I] [DecidableEq J]
    (p : I → Prop) (f : I → J) (K : Finset J) (W : I → ℝ)
    {F₀ : Fintype {t : I // p t ∧ f t ∈ K}}
    {F₁ : ∀ k, Fintype {t : I // p t ∧ f t = k}} :
    (∑ t ∈ @Finset.univ {t : I // p t ∧ f t ∈ K} F₀, W t.val) =
      ∑ k ∈ K, ∑ t ∈ @Finset.univ {t : I // p t ∧ f t = k} (F₁ k), W t.val := by
  classical
  calc
    _ = ∑ t ∈ Finset.univ.filter (fun t ↦ p t ∧ f t ∈ K), W t := by
      rw [Finset.sum_subtype (p := fun t ↦ p t ∧ f t ∈ K) (F := F₀) _ (by simp) W]
    _ = ∑ k ∈ K, ∑ t ∈ (Finset.univ.filter p).filter (fun t ↦ f t = k), W t := by
      simpa only [Finset.filter_filter] using
        (Finset.sum_fiberwise_eq_sum_filter (Finset.univ.filter p) K f W).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_subtype (p := fun t ↦ p t ∧ f t = k) (F := F₁ k) _ (by simp) W]

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def embeddingMarks {n q : ℕ} {G : SimpleGraph (Fin n)} (x : Fin n → S)
    (t : Fin q ↪ G.ConnectedComponent) : Fin q → ProbabilityMeasure S :=
  fun i ↦ componentMark x (t i)

def fixedSurplusMarkedCount {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (K : Finset (Fin q → ℕ)) (r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) : ℝ := by
  classical
  exact ∑ t : {t : Fin q ↪ G.ConnectedComponent // sizes t ∈ K ∧ surpluses t = r},
    Ψ (embeddingMarks x t.val)

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem markedCount_eq_fibre_sum {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    markedCount x G k r Ψ =
      ∑ t : {t : Fin q ↪ G.ConnectedComponent // sizes t = k ∧ surpluses t = r},
        Ψ (embeddingMarks x t.val) := by
  classical
  have hp (t : Fin q ↪ G.ConnectedComponent) :
      (∀ i, componentSize (t i) = k i ∧ componentSurplus (t i) = r i) ↔
        sizes t = k ∧ surpluses t = r := by
    simp only [sizes,surpluses,funext_iff,forall_and]
  let e : GoodComponentTuples G k r ≃
      {t : Fin q ↪ G.ConnectedComponent // sizes t = k ∧ surpluses t = r} :=
    Equiv.subtypeEquivRight hp
  unfold markedCount
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem fixedSurplusMarkedCount_eq_sum {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (K : Finset (Fin q → ℕ)) (r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    fixedSurplusMarkedCount x G K r Ψ = ∑ k ∈ K, markedCount x G k r Ψ := by
  classical
  unfold fixedSurplusMarkedCount
  calc
    _ = ∑ t : {t : Fin q ↪ G.ConnectedComponent // surpluses t = r ∧ sizes t ∈ K},
        Ψ (embeddingMarks x t.val) := by
      apply Fintype.sum_equiv (Equiv.subtypeEquivRight (fun _ ↦ and_comm))
      intro t
      rfl
    _ = ∑ k ∈ K, ∑ t : {t : Fin q ↪ G.ConnectedComponent // surpluses t = r ∧ sizes t = k},
        Ψ (embeddingMarks x t.val) :=
      sum_mem_eq_sum_fibres (fun t : Fin q ↪ G.ConnectedComponent ↦ surpluses t = r)
        (fun t ↦ sizes t) K (fun t ↦ Ψ (embeddingMarks x t))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [markedCount_eq_fibre_sum]
      apply Fintype.sum_equiv (Equiv.subtypeEquivRight (fun _ ↦ and_comm))
      intro t
      rfl

def gridMarkedCount {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (K L : Finset (Fin q → ℕ)) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) : ℝ := by
  classical
  exact ∑ t : {t : Fin q ↪ G.ConnectedComponent // sizes t ∈ K ∧ surpluses t ∈ L},
    Ψ (embeddingMarks x t.val)

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem gridMarkedCount_eq_sum {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (K L : Finset (Fin q → ℕ)) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    gridMarkedCount x G K L Ψ = ∑ r ∈ L, ∑ k ∈ K, markedCount x G k r Ψ := by
  classical
  unfold gridMarkedCount
  calc
    _ = ∑ r ∈ L, fixedSurplusMarkedCount x G K r Ψ :=
      sum_mem_eq_sum_fibres (fun t : Fin q ↪ G.ConnectedComponent ↦ sizes t ∈ K)
        (fun t ↦ surpluses t) L (fun t ↦ Ψ (embeddingMarks x t))
    _ = _ := Finset.sum_congr rfl (fun r _ ↦ fixedSurplusMarkedCount_eq_sum x G K r Ψ)

/-- A literal sum over actual ordered distinct components inside the
requested size/surplus window, carrying each empirical type mark. -/
def windowMarkedCount {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (a b : ℝ) (R : ℕ) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) : ℝ :=
  ∑ t : Fin q ↪ WindowComponent a b R 1 G,
    Ψ (fun i ↦ componentMark x (t i).val)

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem windowMarkedCount_eq_grid {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (hn : 0 < n) (a b : ℝ) (hb : 0 ≤ b) (R : ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    windowMarkedCount x G a b R Ψ =
      gridMarkedCount x G (integerWindow ((n : ℝ)^(2/3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b))
        (surplusIndices q R) Ψ := by
  classical
  have hh : 0 < (n : ℝ)^(2/3 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hp (t : Fin q ↪ G.ConnectedComponent) :
      (∀ i, componentAtom 1 (t i) ∈ windowSet a b R) ↔
        sizes t ∈ integerWindow ((n : ℝ)^(2/3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b) ∧
          surpluses t ∈ surplusIndices q R := by
      rw [mem_integerWindow hh _ _ (fun _ ↦ hb),mem_surplusIndices]
      simp only [sizes,surpluses,componentAtom,windowSet,one_mul,Set.mem_prod,Set.mem_Iic,forall_and]
  let e := (windowTupleEquiv (q := q) G a b R).trans (Equiv.subtypeEquivRight hp)
  unfold windowMarkedCount gridMarkedCount
  apply Fintype.sum_equiv e
  intro t
  rfl

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem windowMarkedCount_eq_sum {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (hn : 0 < n) (a b : ℝ) (hb : 0 ≤ b) (R : ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    windowMarkedCount x G a b R Ψ =
      ∑ r ∈ surplusIndices q R,
        ∑ k ∈ integerWindow ((n : ℝ)^(2/3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b),
          markedCount x G k r Ψ := by
  rw [windowMarkedCount_eq_grid x G hn a b hb R Ψ,gridMarkedCount_eq_sum]

theorem windowMarkedCount_continuous_slice {n q : ℕ} (G : SimpleGraph (Fin n))
    (a b : ℝ) (R : ℕ) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Continuous (fun x : Fin n → S ↦ windowMarkedCount x G a b R Ψ) := by
  apply continuous_finsetSum
  intro t _
  exact hΨ.comp (continuous_pi (fun i ↦ componentMark_continuous (t i).val))

theorem windowMarkedCount_integrable (M : CompactBJRModel S) (lambda a b : ℝ)
    (R n : ℕ) {q : ℕ} (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Integrable (fun p ↦ windowMarkedCount p.1 (AnnealedTypedGraph.graph p) a b R Ψ)
      (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n) :=
  typedObservable_integrable_of_continuous_slices M _ _ _ (fun ea ↦ by
    change Continuous (fun x : Fin n → S ↦ windowMarkedCount x (toGraph ea) a b R Ψ)
    exact windowMarkedCount_continuous_slice (toGraph ea) a b R Ψ hΨ)

theorem windowMarkedCount_expectation_eq_sum (M : CompactBJRModel S) (lambda a b : ℝ)
    (hb : 0 ≤ b) (R n : ℕ) (hn : 0 < n) {q : ℕ}
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    (∫ p, windowMarkedCount p.1 (AnnealedTypedGraph.graph p) a b R Ψ
      ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n) =
      ∑ r ∈ surplusIndices q R,
        ∑ k ∈ integerWindow ((n : ℝ)^(2/3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b),
          ∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ
            ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
              (CriticalScaling.time_nonneg lambda n) n := by
  simp_rw [windowMarkedCount_eq_sum _ _ hn a b hb R Ψ]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    exact integral_finsetSum _ (fun k _ ↦ typedObservable_integrable_of_continuous_slices M _ _ _
      (fun a ↦ by
        change Continuous (fun x : Fin n → S ↦ markedCount x (toGraph a) k r Ψ)
        exact markedCount_continuous_slice (toGraph a) k r Ψ hΨ))
  · intro r _
    exact integrable_finsetSum _ (fun k _ ↦ typedObservable_integrable_of_continuous_slices M _ _ _
      (fun a ↦ by
        change Continuous (fun x : Fin n → S ↦ markedCount x (toGraph a) k r Ψ)
        exact markedCount_continuous_slice (toGraph a) k r Ψ hΨ))

end PerronWright.ComponentWindowMarkedCounts
