import PerronWright.Probability.ComponentWindowCounts
import PerronWright.Probability.CompactAnnealedFactorialBound

/-!
# Tightness of genuine compact-window component laws

The actual integer-size first factorial bound gives a uniform first
mass moment after summing the literal size-surplus cells. The finitely
many small graphs are absorbed explicitly, and bounded point mass is
compact in the actual weak point-measure space.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical ENNReal NNReal Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.ComponentWindowTightness

open ComponentCounts ComponentPointProcesses ComponentWindowPointMeasures
open ComponentWindowCounts FinitePointMeasureCompact

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem exists_eventual_window_mass_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
      (∫ η, (mass η : ℝ) ∂(windowLaw M lambda a b R c n :
        Measure (PointMeasure (SurplusWindow a b R)))) ≤ B := by
  have hac : 0 < a / c := div_pos ha hc
  have habc : a / c ≤ b / c := div_le_div_of_nonneg_right hab hc.le
  obtain ⟨B, hB, hbound⟩ :=
    CompactAnnealedFactorialBound.exists_integer_tuple_expectation_bound M hM hQP
      (q := 1) (by omega) R lambda (a / c) (b / c) hac habc
  let D := (b / c + 1) * (R + 1 : ℕ) * B
  have hbc : 0 < b / c := hac.trans_le habc
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with n hn hn1
  let d : ℝ := (n : ℝ) ^ (2 / 3 : ℝ)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hd1 : 1 ≤ d := Real.one_le_rpow hnR (by norm_num)
  have hd : 0 < d := zero_lt_one.trans_le hd1
  let K := ⌊(b / c) * d⌋₊
  have hnorm (k : ℕ)
      (hk : c * (k : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b) :
      (k : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc (a / c) (b / c) := by
    constructor
    · apply (div_le_iff₀ hc).mpr
      simpa only [mul_div_assoc, mul_comm] using hk.1
    · apply (le_div_iff₀ hc).mpr
      simpa only [mul_div_assoc, mul_comm] using hk.2
  have hK (G : SimpleGraph (Fin n)) (C : G.ConnectedComponent)
      (hC : componentAtom c C ∈ windowSet a b R) : componentSize C ≤ K := by
    apply Nat.le_floor
    exact (div_le_iff₀ hd).mp (hnorm (componentSize C) hC.1).2
  rw [windowLaw_first_mass_sum M lambda a b R c n K hK]
  have hsum : (∑ k ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (R + 1),
      if c * (k : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b then
        (∫ G, (ComponentCounts.count G (fun _ : Fin 1 ↦ k) (fun _ ↦ r) : ℝ)
          ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
            (CriticalScaling.time_nonneg lambda n) n) else 0) ≤
      ∑ _k ∈ Finset.range (K + 1), ∑ _r ∈ Finset.range (R + 1), B / d := by
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro r hr
    split_ifs with hk
    · have hh := hn (fun _ : Fin 1 ↦ k) (fun _ ↦ r)
        (fun _ ↦ Nat.le_of_lt_succ (Finset.mem_range.mp hr))
        (fun _ ↦ hnorm k hk)
      norm_num only [Nat.cast_one, mul_one] at hh
      exact hh
    · exact div_nonneg hB.le hd.le
  apply hsum.trans
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfloor : (K : ℝ) ≤ (b / c) * d := Nat.floor_le (by positivity)
  have hKbound : ((K + 1 : ℕ) : ℝ) / d ≤ b / c + 1 := by
    apply (div_le_iff₀ hd).mpr
    push_cast
    nlinarith
  dsimp [D]
  calc
    ((K + 1 : ℕ) : ℝ) * (((R + 1 : ℕ) : ℝ) * (B / d)) =
        (((K + 1 : ℕ) : ℝ) / d) * ((R + 1 : ℕ) : ℝ) * B := by ring
    _ ≤ (b / c + 1) * ((R + 1 : ℕ) : ℝ) * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKbound (Nat.cast_nonneg _)) hB.le

/-- A finite prefix cannot obstruct a genuine uniform first-mass bound. -/
theorem exists_window_mass_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      (∫ η, (mass η : ℝ) ∂(windowLaw M lambda a b R c n :
        Measure (PointMeasure (SurplusWindow a b R)))) ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_eventual_window_mass_bound M hM hQP lambda a b ha hab R c hc
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  let F (n : ℕ) := ∫ η, (mass η : ℝ) ∂(windowLaw M lambda a b R c n :
    Measure (PointMeasure (SurplusWindow a b R)))
  let B' := B + ∑ n ∈ Finset.range N, |F n|
  have hs : 0 ≤ ∑ n ∈ Finset.range N, |F n| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  refine ⟨B', by dsimp [B']; positivity, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (by dsimp [B']; linarith)
  · have hm : n ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
    have hl := Finset.single_le_sum (fun i _ ↦ abs_nonneg (F i)) hm
    have habs : F n ≤ |F n| := le_abs_self _
    dsimp only [B']
    change F n ≤ B + _
    linarith

/-- Actual law tightness, derived from the graph factorial theorem and
the proved compactness of bounded-mass integer point measures. -/
theorem isTight_windowLaws (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (c : ℝ) (hc : 0 < c) :
    IsTightMeasureSet (Set.range (fun n ↦ (windowLaw M lambda a b R c n :
      Measure (PointMeasure (SurplusWindow a b R))))) := by
  obtain ⟨B, hB, hb⟩ := exists_window_mass_bound M hM hQP lambda a b ha hab R c hc
  exact isTightMeasureSet_of_mass_moment_bound (windowLaw M lambda a b R c)
    (windowLaw_mass_integrable M lambda a b R c) B hB hb

theorem isCompact_closure_windowLaws (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (c : ℝ) (hc : 0 < c) :
    IsCompact (closure (Set.range (windowLaw M lambda a b R c))) := by
  obtain ⟨B, hB, hb⟩ := exists_window_mass_bound M hM hQP lambda a b ha hab R c hc
  exact isCompact_closure_of_mass_moment_bound (windowLaw M lambda a b R c)
    (windowLaw_mass_integrable M lambda a b R c) B hB hb

theorem isTight_unmarkedWindowLaws (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    IsTightMeasureSet (Set.range (fun n ↦ (unmarkedWindowLaw M lambda a b R n :
      Measure (PointMeasure (SurplusWindow a b R))))) :=
  isTight_windowLaws M hM hQP lambda a b ha hab R 1 zero_lt_one

theorem isTight_starredWindowLaws (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    IsTightMeasureSet (Set.range (fun n ↦ (starredWindowLaw M hM lambda a b R n :
      Measure (PointMeasure (SurplusWindow a b R))))) :=
  isTight_windowLaws M hM hQP lambda a b ha hab R (sizeScale M hM) (sizeScale_pos M hM)

end PerronWright.ComponentWindowTightness
