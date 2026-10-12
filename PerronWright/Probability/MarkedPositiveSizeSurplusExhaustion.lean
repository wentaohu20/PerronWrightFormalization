import PerronWright.Probability.ComponentGlobalMarkedProcess
import PerronWright.Probability.PositiveSizeSurplusExhaustion

/-! # Actual compact exhaustion of the empirical-marked positive ground space

Compactness of the probability-mark factor is inherited from its proved
homeomorphism to the actual compact probability-measure space. The
literal canonical size-surplus windows times that whole mark space are
compact, strictly interior-nested, and cover the actual marked space.
-/

open MeasureTheory Topology
open scoped Classical CompactlySupported

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.MarkedPositiveSizeSurplusExhaustion

open ComponentGlobalPointProcess ComponentGlobalMarkedProcess WeakProbabilityMarks
open PositiveSizeSurplusExhaustion

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

def window (m : ℕ) : Set (MarkedPositiveSizeSurplus S) :=
  markedWindowSet (lower m) (upper m) m

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem window_eq_prod (m : ℕ) : window (S := S) m =
    (PositiveSizeSurplusExhaustion.window m).prod Set.univ := by
  ext z
  change z.1 ∈ positiveWindowSet (lower m) (upper m) m ↔
    z.1 ∈ positiveWindowSet (lower m) (upper m) m ∧ z.2 ∈ Set.univ
  simp

theorem isCompact_window (m : ℕ) : IsCompact (window (S := S) m) := by
  rw [window_eq_prod]
  exact (PositiveSizeSurplusExhaustion.isCompact_window m).prod isCompact_univ

omit [CompactSpace S] in
theorem window_subset_interior_succ (m : ℕ) :
    window (S := S) m ⊆ interior (window (S := S) (m + 1)) := by
  intro z hz
  apply preimage_interior_subset_interior_preimage continuous_fst
  exact PositiveSizeSurplusExhaustion.window_subset_interior_succ m hz

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem iUnion_window : (⋃ m, window (S := S) m) = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hz : z.1 ∈ ⋃ m, PositiveSizeSurplusExhaustion.window m := by
    rw [PositiveSizeSurplusExhaustion.iUnion_window]
    trivial
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hz
  exact ⟨m, hm⟩

def exhaustion : CompactExhaustion (MarkedPositiveSizeSurplus S) where
  toFun := window
  isCompact' := isCompact_window
  subset_interior_succ' := window_subset_interior_succ
  iUnion_eq' := iUnion_window

theorem exists_compact_subset_window {K : Set (MarkedPositiveSizeSurplus S)} (hK : IsCompact K) :
    ∃ m, K ⊆ window m := exhaustion.exists_superset_of_isCompact hK

theorem exists_support_subset_window (f : C_c(MarkedPositiveSizeSurplus S, ℝ)) :
    ∃ m, tsupport f ⊆ window m := exists_compact_subset_window f.hasCompactSupport

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem range_markedPositiveWindowEmbedding (a b : ℝ) (R : ℕ) (ha : 0 < a) :
    Set.range (markedPositiveWindowEmbedding (S := S) a b R ha) = markedWindowSet a b R := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    apply (range_positiveWindowEmbedding a b R ha).le
    exact ⟨x.1, rfl⟩
  · intro hz
    obtain ⟨x, hx⟩ := (range_positiveWindowEmbedding a b R ha).ge hz
    exact ⟨(x, z.2), Prod.ext hx rfl⟩

end PerronWright.MarkedPositiveSizeSurplusExhaustion
