import PerronWright.Analysis.CompactSequentialUniform
import Mathlib.Order.Filter.AtTopBot.Finite

/-! # Compact parameter uniformity from actual varying-sequence estimates

This elementary compactness lemma does not supply a graph asymptotic.
Applications must prove its sequence estimate for their literal source.
A convergent parameter subsequence is extended to all integer sizes,
so results stated for actual full varying sequences suffice.
-/

open Filter Topology
open scoped Classical
noncomputable section

namespace PerronWright.CountableFixedSupportSequentialParameter

variable {X : Type*} [PseudoMetricSpace X]

def extendParameter (N : ℕ → ℕ) (x : ℕ → X) (s : X) (n : ℕ) : X :=
  if h : ∃ j, N j = n then x (Classical.choose h) else s

omit [PseudoMetricSpace X] in
theorem extendParameter_apply (N : ℕ → ℕ) (hN : StrictMono N)
    (x : ℕ → X) (s : X) (j : ℕ) : extendParameter N x s (N j) = x j := by
  unfold extendParameter
  split_ifs with h
  · rw [hN.injective (Classical.choose_spec h)]
  · exact False.elim (h ⟨j, rfl⟩)

theorem tendsto_extendParameter (N : ℕ → ℕ) (hN : StrictMono N)
    (x : ℕ → X) (s : X) (hx : Tendsto x atTop (𝓝 s)) :
    Tendsto (extendParameter N x s) atTop (𝓝 s) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hx ε hε)
  refine eventually_atTop.mpr ⟨N K, fun n hn ↦ ?_⟩
  unfold extendParameter
  split_ifs with h
  · have he := Classical.choose_spec h
    have hkn : K ≤ Classical.choose h := hN.le_iff_le.mp (by simpa only [he] using hn)
    exact hK _ hkn
  · simpa only [dist_self] using hε

/-- A compactness contradiction upgrades estimates for every genuinely
convergent full parameter sequence to one threshold for the whole compact
parameter set. No continuity or asymptotic of a source is assumed here. -/
theorem eventually_forall_compact_parameters {K : Set X} (hK : IsCompact K)
    (P : ℕ → X → Prop)
    (hseq : ∀ x : ℕ → X, ∀ s ∈ K, Tendsto x atTop (𝓝 s) →
      ∀ᶠ n in atTop, P n (x n)) :
    ∀ᶠ n in atTop, ∀ s ∈ K, P n s := by
  classical
  by_contra hfail
  have hbad : ∀ j : ℕ, ∃ n, j ≤ n ∧ ∃ x ∈ K, ¬ P n x := by
    intro j
    have hnot : ¬ (∀ n, j ≤ n → ∀ x ∈ K, P n x) := by
      intro h
      exact hfail (eventually_atTop.mpr ⟨j, h⟩)
    push Not at hnot
    exact hnot
  choose N hN x hx hb using hbad
  obtain ⟨φ, _, hNφ⟩ := strictMono_subseq_of_id_le hN
  obtain ⟨s, hs, ψ, hψ, hxs⟩ := hK.tendsto_subseq (fun j ↦ hx (φ j))
  let Q : ℕ → ℕ := (N ∘ φ) ∘ ψ
  let z : ℕ → X := (x ∘ φ) ∘ ψ
  have hQ : StrictMono Q := hNφ.comp hψ
  have hz : Tendsto z atTop (𝓝 s) := hxs
  have he := hseq (extendParameter Q z s) s hs (tendsto_extendParameter Q hQ z s hz)
  obtain ⟨j, hj⟩ := (hQ.tendsto_atTop.eventually he).exists
  rw [extendParameter_apply Q hQ z s j] at hj
  exact hb (φ (ψ j)) hj

end PerronWright.CountableFixedSupportSequentialParameter
