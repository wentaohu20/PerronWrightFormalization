import PerronWright.Probability.ComponentWindowPointMeasures

/-!
# Literal size-surplus counts and compact-window first moments

The one-component factorial count is identified with an actual component
fibre. Summing these fibres gives the exact first mass of the graph's
window point measure and its genuine annealed probability law.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.ComponentWindowCounts

open ComponentCounts ComponentBlocks ComponentWindowPointMeasures FinitePointMeasureCompact

def singleComponentEquiv {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    GoodComponentTuples G (fun _ : Fin 1 ↦ k) (fun _ ↦ r) ≃
      {C : G.ConnectedComponent // componentSize C = k ∧ componentSurplus C = r} where
  toFun c := ⟨c.val 0, c.property 0⟩
  invFun C := ⟨⟨fun _ ↦ C.val, fun _ _ _ ↦ Subsingleton.elim _ _⟩, fun _ ↦ C.property⟩
  left_inv c := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    exact congrArg c.val (Subsingleton.elim (0 : Fin 1) i)
  right_inv C := rfl

theorem single_count_eq_card {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    ComponentCounts.count G (fun _ : Fin 1 ↦ k) (fun _ ↦ r) =
      Fintype.card {C : G.ConnectedComponent // componentSize C = k ∧ componentSurplus C = r} :=
  Fintype.card_congr (singleComponentEquiv G k r)

theorem single_count_eq_sum {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    ComponentCounts.count G (fun _ : Fin 1 ↦ k) (fun _ ↦ r) =
      ∑ C : G.ConnectedComponent,
        if componentSize C = k ∧ componentSurplus C = r then 1 else 0 := by
  rw [single_count_eq_card, Fintype.card_subtype]
  exact Finset.card_filter _ _

theorem componentSize_le {n : ℕ} {G : SimpleGraph (Fin n)} (C : G.ConnectedComponent) :
    componentSize C ≤ n := by
  unfold componentSize
  simpa using Finset.card_le_card ((componentBlockEquiv G C).val.subset_univ)

/-- Exact finite first-mass decomposition into the paper's genuine
one-component count variables. The cutoff only needs to cover the
sizes of components actually selected by the window. -/
theorem window_size_eq_sum_single_counts (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ)
    (hK : ∀ C : G.ConnectedComponent,
      componentAtom c C ∈ windowSet a b R → componentSize C ≤ K) :
    size (windowPointMeasure a b R c G) =
      ∑ k ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (R + 1),
        if c * (k : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b then
          ComponentCounts.count G (fun _ : Fin 1 ↦ k) (fun _ ↦ r) else 0 := by
  rw [windowPointMeasure_size]
  change Fintype.card {C : G.ConnectedComponent // componentAtom c C ∈ windowSet a b R} = _
  rw [Fintype.card_subtype, Finset.card_filter]
  simp_rw [single_count_eq_sum, Finset.ite_sum_zero]
  simp_rw [Finset.sum_comm (s := Finset.range (R + 1)) (t := Finset.univ)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  have hterm : ∀ k r : ℕ,
      (if c * (k : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b then
        if componentSize C = k ∧ componentSurplus C = r then 1 else 0 else 0 : ℕ) =
      if k = componentSize C then if r = componentSurplus C then
        if c * (componentSize C : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b
        then 1 else 0 else 0 else 0 := by
    intro k r
    by_cases hk : k = componentSize C <;> by_cases hr : r = componentSurplus C <;>
      simp [hk, hr, eq_comm]
  simp_rw [hterm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_range]
  by_cases hC : componentAtom c C ∈ windowSet a b R
  · have hk := hK C hC
    have hc := hC
    change c * (componentSize C : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b ∧
      componentSurplus C ≤ R at hc
    simp [hC, Nat.lt_succ_iff.mpr hk, Nat.lt_succ_iff.mpr hc.2, hc.1]
  · have hc := hC
    change ¬(c * (componentSize C : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b ∧
      componentSurplus C ≤ R) at hc
    by_cases hp : c * (componentSize C : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b
    · have hr : ¬componentSurplus C ≤ R := fun hr ↦ hc ⟨hp, hr⟩
      simp [hC, hr]
    · simp [hC, hp]

theorem window_size_eq_sum_single_counts_n (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    size (windowPointMeasure a b R c G) =
      ∑ k ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (R + 1),
        if c * (k : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b then
          ComponentCounts.count G (fun _ : Fin 1 ↦ k) (fun _ ↦ r) else 0 :=
  window_size_eq_sum_single_counts a b R c G n (fun C _ ↦ componentSize_le C)

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

theorem windowLaw_first_mass_sum (M : CompactBJRModel S)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n K : ℕ)
    (hK : ∀ (G : SimpleGraph (Fin n)) (C : G.ConnectedComponent),
      componentAtom c C ∈ windowSet a b R → componentSize C ≤ K) :
    (∫ η, (mass η : ℝ) ∂(windowLaw M lambda a b R c n :
      Measure (PointMeasure (SurplusWindow a b R)))) =
      ∑ k ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (R + 1),
        if c * (k : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b then
          (∫ G, (ComponentCounts.count G (fun _ : Fin 1 ↦ k) (fun _ ↦ r) : ℝ)
            ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
              (CriticalScaling.time_nonneg lambda n) n) else 0 := by
  rw [windowLaw_mass_integral]
  have he : ∀ G : SimpleGraph (Fin n),
      (Fintype.card (WindowComponent a b R c G) : ℝ) =
      ∑ k ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (R + 1),
        if c * (k : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b then
          (ComponentCounts.count G (fun _ : Fin 1 ↦ k) (fun _ ↦ r) : ℝ) else 0 := by
    intro G
    have hh := window_size_eq_sum_single_counts a b R c G K (hK G)
    rw [windowPointMeasure_size] at hh
    exact_mod_cast hh
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp
    · intro _ _
      exact Integrable.of_finite
  · intro _ _
    exact Integrable.of_finite

theorem windowLaw_first_mass_sum_n (M : CompactBJRModel S)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    (∫ η, (mass η : ℝ) ∂(windowLaw M lambda a b R c n :
      Measure (PointMeasure (SurplusWindow a b R)))) =
      ∑ k ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (R + 1),
        if c * (k : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) ∈ Set.Icc a b then
          (∫ G, (ComponentCounts.count G (fun _ : Fin 1 ↦ k) (fun _ ↦ r) : ℝ)
            ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
              (CriticalScaling.time_nonneg lambda n) n) else 0 :=
  windowLaw_first_mass_sum M lambda a b R c n n (fun _ C _ ↦ componentSize_le C)

end PerronWright.ComponentWindowCounts
