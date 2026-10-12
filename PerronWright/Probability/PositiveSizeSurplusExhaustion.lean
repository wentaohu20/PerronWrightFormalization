import PerronWright.Probability.ComponentGlobalPointProcess
import PerronWright.Probability.ComponentWindowTightness

/-!
# A literal compact exhaustion of positive size times surplus

The canonical windows `[1/(m+1), m+1] × {0,...,m}` form a genuine
compact exhaustion, including strict interior nesting. Their actual
graph counts have uniformly bounded first moments. This supplies local
mass control, not an assumed global tightness theorem.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported ENNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.PositiveSizeSurplusExhaustion

open ComponentGlobalPointProcess ComponentWindowPointMeasures
open FinitePointMeasureCompact

def lower (m : ℕ) : ℝ := 1 / (m + 1 : ℝ)

def upper (m : ℕ) : ℝ := (m + 1 : ℝ)

theorem lower_pos (m : ℕ) : 0 < lower m := by unfold lower; positivity

theorem lower_le_upper (m : ℕ) : lower m ≤ upper m := by
  unfold lower upper
  apply (div_le_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

def window (m : ℕ) : Set PositiveSizeSurplus := positiveWindowSet (lower m) (upper m) m

theorem isCompact_window (m : ℕ) : IsCompact (window m) :=
  isCompact_positiveWindowSet _ _ _ (lower_pos m)

theorem window_subset_interior_succ (m : ℕ) : window m ⊆ interior (window (m + 1)) := by
  let U : Set PositiveSizeSurplus :=
    {z | lower (m + 1) < z.1.val ∧ z.1.val < upper (m + 1)} ∩ {z | z.2 ≤ m + 1}
  apply subset_interior_iff.mpr
  refine ⟨U, ?_, ?_, ?_⟩
  · exact (isOpen_Ioo.preimage (continuous_subtype_val.comp continuous_fst)).inter
      ((isOpen_discrete (Set.Iic (m + 1))).preimage continuous_snd)
  · intro z hz
    refine ⟨⟨lt_of_lt_of_le ?_ hz.1.1, lt_of_le_of_lt hz.1.2 ?_⟩,
      Nat.le_succ_of_le hz.2⟩
    · unfold lower
      apply one_div_lt_one_div_of_lt (by positivity)
      push_cast
      linarith
    · unfold upper
      push_cast
      linarith
  · intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩

theorem iUnion_window : (⋃ m, window m) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < z.1.val from z.1.property)
  obtain ⟨l, hl⟩ := exists_nat_gt z.1.val
  let m := max (max k l) z.2
  have hkm : k ≤ m := (le_max_left k l).trans (le_max_left _ _)
  have hlm : l ≤ m := (le_max_right k l).trans (le_max_left _ _)
  apply Set.mem_iUnion.mpr
  refine ⟨m, ?_⟩
  change (lower m ≤ z.1.val ∧ z.1.val ≤ upper m) ∧ z.2 ≤ m
  refine ⟨⟨?_, ?_⟩, le_max_right (max k l) z.2⟩
  · apply le_trans _ hk.le
    apply one_div_le_one_div_of_le (by positivity : 0 < (k : ℝ) + 1)
    have hcast : (k : ℝ) ≤ m := Nat.cast_le.mpr hkm
    linarith
  · exact hl.le.trans ((Nat.cast_le.mpr hlm).trans (by dsimp [upper]; linarith))

/-- A true compact exhaustion of the paper's ground space. -/
def exhaustion : CompactExhaustion PositiveSizeSurplus where
  toFun := window
  isCompact' := isCompact_window
  subset_interior_succ' := window_subset_interior_succ
  iUnion_eq' := iUnion_window

theorem exists_compact_subset_window {K : Set PositiveSizeSurplus} (hK : IsCompact K) :
    ∃ m, K ⊆ window m := exhaustion.exists_superset_of_isCompact hK

theorem exists_support_subset_window (f : C_c(PositiveSizeSurplus, ℝ)) :
    ∃ m, tsupport f ⊆ window m := exists_compact_subset_window f.hasCompactSupport

theorem unmarkedProcess_window_real_eq_mass (m : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    (unmarkedProcess G : Measure PositiveSizeSurplus).real (window m) =
      (mass (windowPointMeasure (lower m) (upper m) m 1 G) : ℝ) := by
  have h := congrArg (fun μ : Measure PositiveSizeSurplus ↦ μ Set.univ)
    (map_windowPointMeasure_eq_restrict_process (lower m) (upper m) m (lower_pos m) G)
  rw [Measure.map_apply (measurable_positiveWindowEmbedding _ _ _ _) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  rw [measureReal_def, window, ← h]
  simpa only [mass, ENNReal.coe_toReal] using
    congrArg (fun x : ℝ≥0∞ ↦ x.toReal)
      (FiniteMeasure.ennreal_mass (μ := (windowPointMeasure (lower m) (upper m) m 1 G :
        FiniteMeasure (SurplusWindow (lower m) (upper m) m)))).symm

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- True all-size first moments on every member of the literal compact
exhaustion, with the finite prefix included. No local-tightness or
global point-law existence interface is assumed. -/
theorem exists_window_first_moment_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      (∫ G, (unmarkedProcess G : Measure PositiveSizeSurplus).real (window m)
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n) ≤ B := by
  obtain ⟨B, hB, hb⟩ := ComponentWindowTightness.exists_window_mass_bound
    M hM hQP lambda (lower m) (upper m) (lower_pos m) (lower_le_upper m) m 1 zero_lt_one
  refine ⟨B, hB, fun n ↦ ?_⟩
  simpa only [unmarkedProcess_window_real_eq_mass,
    windowPointMeasure_mass, NNReal.coe_natCast, windowLaw_mass_integral] using hb n

end PerronWright.PositiveSizeSurplusExhaustion
