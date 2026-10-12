import PerronWright.Probability.CountableEmpiricalFiniteModel

/-! # Fixed literal truncated reference models and actual rounded vertices

The reference law is the normalized retained mass, extended by zero. Its
critical finite model is fixed while the actual rounded vertex counts vary.
The count discrepancies are proved from the literal integer construction.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open GrowingTypeCounts
open CountableTypeRealization (weights vertexTypes vertexTypes_lt)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

def fixedSupportWeights (M : CountableKernel) (m a : ℕ) : ℝ :=
  if ha : a < m + 1 then truncatedLaw (weights M) m ⟨a, ha⟩ else 0

theorem fixedSupportWeights_fin (M : CountableKernel) (m : ℕ) (a : Fin (m + 1)) :
    M.fixedSupportWeights m a = truncatedLaw (weights M) m a := by
  simp only [fixedSupportWeights, dif_pos a.isLt]

theorem fixedSupportWeights_nonneg (M : CountableKernel) (m a : ℕ) :
    0 ≤ M.fixedSupportWeights m a := by
  unfold fixedSupportWeights
  split_ifs with ha
  · exact (truncatedLaw_pos (weights M) M.atomMass_pos m ⟨a, ha⟩).le
  · exact le_rfl

theorem fixedSupportWeights_zero (M : CountableKernel) (m a : ℕ)
    (ha : a ∉ Finset.range (m + 1)) : M.fixedSupportWeights m a = 0 := by
  exact dif_neg (by simpa only [Finset.mem_range] using ha)

theorem fixedSupportWeights_pos (M : CountableKernel) (m a : ℕ)
    (ha : a ∈ Finset.range (m + 1)) : 0 < M.fixedSupportWeights m a := by
  rw [fixedSupportWeights, dif_pos (Finset.mem_range.mp ha)]
  exact truncatedLaw_pos (weights M) M.atomMass_pos m _

theorem fixedSupportWeights_hasSum (M : CountableKernel) (m : ℕ) :
    HasSum (M.fixedSupportWeights m) 1 := by
  have hs : (∑ a ∈ Finset.range (m + 1), M.fixedSupportWeights m a) = 1 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp_rw [M.fixedSupportWeights_fin]
    exact sum_truncatedLaw (weights M) M.atomMass_pos m
  simpa only [hs] using hasSum_sum_of_ne_finset_zero (M.fixedSupportWeights_zero m)

def fixedSupportSpectralRadius (M : CountableKernel) (m : ℕ) : ℝ :=
  M.weightedSpectralRadius (M.fixedSupportWeights m) (M.fixedSupportWeights_nonneg m)
    (M.fixedSupportWeights_hasSum m)

theorem fixedSupportSpectralRadius_pos (M : CountableKernel) (m : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    0 < M.fixedSupportSpectralRadius m :=
  (M.exists_nonnegative_weighted_perron _ _ _ (Finset.range (m + 1))
    (M.fixedSupportWeights_zero m) hlower hlo).1

def fixedSupportModel (M : CountableKernel) (m : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    FiniteIrreducibleModel (Finset.range (m + 1)) :=
  M.finiteCriticalModel (M.fixedSupportWeights m) (M.fixedSupportWeights_nonneg m)
    (M.fixedSupportWeights_hasSum m) (Finset.range (m + 1))
    (M.fixedSupportWeights_zero m) (M.fixedSupportWeights_pos m) hlower hlo

theorem fixedSupportModel_isCritical (M : CountableKernel) (m : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    (M.fixedSupportModel m hlower hlo).IsCritical :=
  M.finiteCriticalModel_isCritical _ _ _ _ _ _ hlower hlo

theorem fixedSupportModel_weight (M : CountableKernel) (m : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (a : Finset.range (m + 1)) :
    (M.fixedSupportModel m hlower hlo).weight a =
      truncatedLaw (weights M) m ⟨a, Finset.mem_range.mp a.property⟩ := by
  exact M.fixedSupportWeights_fin m ⟨a, Finset.mem_range.mp a.property⟩

def fixedSupportVertexTypes (M : CountableKernel) (m n : ℕ) (v : Fin n) :
    Finset.range (m + 1) :=
  ⟨vertexTypes M m n v, Finset.mem_range.mpr (vertexTypes_lt M m n v)⟩

theorem fixedSupportVertexTypes_fiberCount (M : CountableKernel) (m n : ℕ)
    (a : Finset.range (m + 1)) :
    fiberCount (M.fixedSupportVertexTypes m n) a =
      truncatedCounts (weights M) m n ⟨a, Finset.mem_range.mp a.property⟩ := by
  unfold fiberCount
  have he : ∀ v : Fin n, M.fixedSupportVertexTypes m n v = a ↔ vertexTypes M m n v = a.val :=
    fun _ ↦ ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
  rw [Fintype.card_eq_nat_card]
  calc
    _ = Nat.card {v : Fin n // vertexTypes M m n v = a.val} :=
      Nat.card_congr (Equiv.subtypeEquivRight he)
    _ = _ := by
      rw [← Fintype.card_eq_nat_card, CountableTypeRealization.fiber_card,
        dif_pos (Finset.mem_range.mp a.property)]

/-- Actual deterministic count errors, valid at every size, including zero. -/
theorem fixedSupportVertexTypes_rounding_bound (M : CountableKernel) (m n : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (a : Finset.range (m + 1)) :
    |(fiberCount (M.fixedSupportVertexTypes m n) a : ℝ) -
      (n : ℝ) * (M.fixedSupportModel m hlower hlo).weight a| ≤ 2 * (m + 1 : ℝ) := by
  rw [M.fixedSupportVertexTypes_fiberCount, M.fixedSupportModel_weight]
  have hs := FiniteTypeCounts.sum_counts_error_le (0 : Fin (m + 1))
    (truncatedLaw (weights M) m) (fun a ↦ (truncatedLaw_pos (weights M) M.atomMass_pos m a).le)
    (sum_truncatedLaw (weights M) M.atomMass_pos m) n
  have hi := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin (m + 1)))) ↦
    abs_nonneg ((FiniteTypeCounts.counts 0 (truncatedLaw (weights M) m) n b : ℝ) -
      (n : ℝ) * truncatedLaw (weights M) m b))
    (Finset.mem_univ (⟨a, Finset.mem_range.mp a.property⟩ : Fin (m + 1)))
  exact hi.trans (by simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hs)

end PerronWright.CountableKernel
