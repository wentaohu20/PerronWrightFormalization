import PerronWright.Kernel.CountableApproximationEmpirical
import PerronWright.Probability.CountableFiniteGraphMarkBridge
import PerronWright.Probability.FiniteIrreducibleTypePlacementMultiplicity

/-! # Actual empirical retained finite models and vertex populations

Index n uses the already constructed n+1 vertices. Their finite-support
type assignment has exactly (n+1) times the empirical type weights.
Positive retained counts give a genuine critical finite model at each
index, rather than an assumed model bridge.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical
noncomputable section

namespace PerronWright.CountableKernel

theorem empiricalWeights_pos_of_counts (M : CountableKernel) (level : ℕ → ℕ)
    (hcounts : ∀ n > 0, ∀ a, 0 < GrowingTypeCounts.truncatedCounts
      (CountableTypeRealization.weights M) (level n) n a)
    (n a : ℕ) (ha : a ∈ Finset.range (level (n + 1) + 1)) :
    0 < M.empiricalWeights level n a := by
  rw [empiricalWeights, CountableTypeRealization.empiricalMeasure_atom]
  have ha' := Finset.mem_range.mp ha
  rw [GrowingTypeCounts.extendedLaw, dif_pos ha']
  change 0 < (GrowingTypeCounts.truncatedCounts (CountableTypeRealization.weights M)
    (level (n + 1)) (n + 1) ⟨a, ha'⟩ : ℝ) / (n + 1 : ℕ)
  exact div_pos (Nat.cast_pos.mpr (hcounts (n + 1) (Nat.succ_pos n) _))
    (Nat.cast_pos.mpr (Nat.succ_pos n))

def empiricalVertexTypes (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ)
    (v : Fin (n + 1)) : Finset.range (level (n + 1) + 1) :=
  ⟨CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1) v,
    Finset.mem_range.mpr (CountableTypeRealization.vertexTypes_lt M _ _ v)⟩

theorem empiricalVertexTypes_fiber_count (M : CountableKernel) (level : ℕ → ℕ)
    (n : ℕ) (a : Finset.range (level (n + 1) + 1)) :
    FiniteIrreducibleTypePlacementMultiplicity.fiberCount (M.empiricalVertexTypes level n) a =
      GrowingTypeCounts.truncatedCounts (CountableTypeRealization.weights M)
        (level (n + 1)) (n + 1) ⟨a, Finset.mem_range.mp a.property⟩ := by
  unfold FiniteIrreducibleTypePlacementMultiplicity.fiberCount
  have he : ∀ v : Fin (n + 1), M.empiricalVertexTypes level n v = a ↔
      CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1) v = a.val :=
    fun _ ↦ ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
  rw [Fintype.card_eq_nat_card]
  calc
    _ = Nat.card {v : Fin (n + 1) //
        CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1) v = a.val} :=
      Nat.card_congr (Equiv.subtypeEquivRight he)
    _ = _ := by
      rw [← Fintype.card_eq_nat_card, CountableTypeRealization.fiber_card,
        dif_pos (Finset.mem_range.mp a.property)]

/-- The constructed vertices have zero discrepancy from their actual
empirical population, not a probabilistic or asymptotic count premise. -/
theorem empiricalVertexTypes_exact_weights (M : CountableKernel) (level : ℕ → ℕ)
    (n : ℕ) (a : Finset.range (level (n + 1) + 1)) :
    (FiniteIrreducibleTypePlacementMultiplicity.fiberCount
      (M.empiricalVertexTypes level n) a : ℝ) =
      (n + 1 : ℕ) * M.empiricalWeights level n a := by
  rw [M.empiricalVertexTypes_fiber_count, empiricalWeights,
    CountableTypeRealization.empiricalMeasure_atom, GrowingTypeCounts.extendedLaw,
    dif_pos (Finset.mem_range.mp a.property)]
  change _ = ((n + 1 : ℕ) : ℝ) *
    ((GrowingTypeCounts.truncatedCounts (CountableTypeRealization.weights M)
      (level (n + 1)) (n + 1) ⟨a, Finset.mem_range.mp a.property⟩ : ℝ) / (n + 1 : ℕ))
  rw [mul_div_cancel₀ _ (Nat.cast_pos.mpr (Nat.succ_pos n)).ne']

def empiricalFiniteModel (M : CountableKernel) (level : ℕ → ℕ)
    (hpos : ∀ n a, a ∈ Finset.range (level (n + 1) + 1) → 0 < M.empiricalWeights level n a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (n : ℕ) :
    FiniteIrreducibleModel (Finset.range (level (n + 1) + 1)) :=
  M.finiteCriticalModel (M.empiricalWeights level n) (M.empiricalWeights_nonneg level n)
    (M.empiricalWeights_hasSum level n) (Finset.range (level (n + 1) + 1))
    (M.empiricalWeights_finite_support level n) (hpos n) hlower hlo

theorem empiricalFiniteModel_isCritical (M : CountableKernel) (level : ℕ → ℕ)
    (hpos : ∀ n a, a ∈ Finset.range (level (n + 1) + 1) → 0 < M.empiricalWeights level n a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (n : ℕ) :
    (M.empiricalFiniteModel level hpos hlower hlo n).IsCritical :=
  M.finiteCriticalModel_isCritical _ _ _ _ _ (hpos n) hlower hlo

end PerronWright.CountableKernel
