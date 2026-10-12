import PerronWright.Probability.AnnealedMarkedResidualTests

/-!
# Literal continuous-mark ordered component tuple counts

The count is a finite sum over actual distinct connected components of
the sampled graph, carrying their actual empirical sampled-type marks.
Its passage to ambient labelled placements uses the proved component
and block equivalences and the exact internal labelling multiplicity.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedMarkedFactorialCounting

open ComponentBlocks ComponentCounts EmpiricalTypeMarks EmpiricalMarkConcentration
  AnnealedTupleResidualCounting AnnealedMarkedResidualTests

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def tupleMarks {n q : ℕ} {G : SimpleGraph (Fin n)} {k r : Fin q → ℕ}
    (x : Fin n → S) (c : GoodComponentTuples G k r) : Fin q → ProbabilityMeasure S :=
  fun i ↦ componentMark x (c.val i)

/-- Actual ordered distinct component tuples, with an arbitrary coupled
continuous joint mark test, not a product or pooled mark substitute. -/
def markedCount {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) : ℝ :=
  ∑ c : GoodComponentTuples G k r, Ψ (tupleMarks x c)

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem markedCount_one {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) : markedCount x G k r (fun _ ↦ 1) = (count G k r:ℝ) := by
  simp only [markedCount,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,count]

theorem componentMark_continuous {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) : Continuous (fun x : Fin n → S ↦ componentMark x C) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  exact componentMark_test_continuous C

theorem markedCount_continuous_slice {n q : ℕ} (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Continuous (fun x : Fin n → S ↦ markedCount x G k r Ψ) := by
  apply continuous_finsetSum
  intro c _
  exact hΨ.comp (continuous_pi (fun i ↦ componentMark_continuous (c.val i)))

def blockFamilyMarks {n q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (x : Fin n → S) (B : DisjointBlockFamilies n k) : Fin q → ProbabilityMeasure S :=
  fun i ↦ empiricalProbability x (B.val i) (Finset.card_pos.mp (by rw [B.property.1 i]; exact hk i))

def placementMarks {n q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (f : Placements n k) (x : Fin n → S) : Fin q → ProbabilityMeasure S :=
  fun i ↦ typesMark (hk i) (fun a ↦ x (f ⟨i,a⟩))

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
/-- The literal block empirical measure does not depend on the chosen
internal labelling. This is equality of measures, not only test averages. -/
theorem empiricalProbability_eq_typesMark {n k : ℕ} (hk : 0 < k)
    (x : Fin n → S) (B : Finset (Fin n)) (hB : B.Nonempty) (hc : B.card = k)
    (e : Fin k ≃ ↥B) :
    empiricalProbability x B hB = typesMark hk (fun a ↦ x (e a).val) := by
  apply Subtype.ext
  change empiricalMeasure x B = empiricalMeasure (fun a ↦ x (e a).val) Finset.univ
  unfold empiricalMeasure
  rw [Finset.card_univ,Fintype.card_fin,hc]
  congr 1
  rw [← Finset.sum_coe_sort]
  exact (e.sum_comp (fun v : ↥B ↦ Measure.dirac (x v.val))).symm

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem blockFamilyMarks_familyOfPlacement {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (x : Fin n → S) :
    blockFamilyMarks hk x (familyOfPlacement f) = placementMarks hk f x := by
  funext i
  exact empiricalProbability_eq_typesMark (hk i) x _ _ (blockOfPlacement_card f i) (labelsOfPlacement f i)

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem markedCount_eq_sum_disjointBlocks {n q : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    markedCount x G k r Ψ = ∑ B : DisjointBlockFamilies n k,
      if ∀ i, MatchesBlock G (B.val i) (k i) (r i) then Ψ (blockFamilyMarks hk x B) else 0 := by
  let e := (componentTupleBlockEquiv G k r).trans (goodBlockFamiliesEquiv G k r)
  have hs := Finset.sum_congr_set
    (s := {B : DisjointBlockFamilies n k | ∀ i, MatchesBlock G (B.val i) (k i) (r i)})
    (fun B ↦ if ∀ i, MatchesBlock G (B.val i) (k i) (r i) then Ψ (blockFamilyMarks hk x B) else 0)
    (fun B ↦ Ψ (blockFamilyMarks hk x B.val)) (fun _ h ↦ if_pos h) (fun _ h ↦ if_neg h)
  rw [hs]
  unfold markedCount
  apply Fintype.sum_equiv e
  intro c
  congr 1

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
/-- Every actual marked component tuple has exactly the genuine product
of size factorials many ambient label placements. -/
theorem markedCount_mul_factorials_eq_sum_placements {n q : ℕ}
    (x : Fin n → S) (G : SimpleGraph (Fin n)) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    markedCount x G k r Ψ * (∏ i, ((k i).factorial:ℝ)) = ∑ f : Placements n k,
      if ∀ i, MatchesBlock G (blockOfPlacement f i) (k i) (r i) then Ψ (placementMarks hk f x) else 0 := by
  have hs := sum_placements_eq_factorial_mul_sum_blocks k
    (fun B ↦ if ∀ i, MatchesBlock G (B.val i) (k i) (r i) then Ψ (blockFamilyMarks hk x B) else 0)
  simp_rw [blockFamilyMarks_familyOfPlacement] at hs
  simp only [familyOfPlacement] at hs
  rw [markedCount_eq_sum_disjointBlocks x G k r hk Ψ]
  exact (mul_comm _ _).trans hs.symm

theorem placementMarks_continuous {n q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (f : Placements n k) : Continuous (placementMarks (S := S) hk f) := by
  apply continuous_pi
  intro i
  exact (typesMark_continuous (hk i)).comp
    (continuous_pi (fun a ↦ continuous_apply (f ⟨i,a⟩)))

end PerronWright.AnnealedMarkedFactorialCounting
