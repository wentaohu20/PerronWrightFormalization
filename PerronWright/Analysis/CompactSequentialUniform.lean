import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Basic

/-! # Uniform convergence from proved diagonal limits on a compact set -/

open Filter Topology
open scoped Topology

noncomputable section

namespace PerronWright.CompactSequentialUniform

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A compactness argument upgrading all positive-size diagonal sequence
limits to uniform convergence. The argument is proved here; applications
must prove the diagonal limits from their actual models. -/
theorem uniform_of_diagonal_sequences {K : Set X} (hK : IsCompact K)
    (F : ℕ → X → Y) (f : X → Y) (hf : ContinuousOn f K)
    (hseq : ∀ (N : ℕ → ℕ), (∀ m, 0 < N m) → Tendsto N atTop atTop →
      ∀ (x : ℕ → X), (∀ m, x m ∈ K) → ∀ s ∈ K,
        Tendsto x atTop (𝓝 s) → Tendsto (fun m ↦ F (N m) (x m)) atTop (𝓝 (f s))) :
    TendstoUniformlyOn F f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hfail
  have hbad : ∀ m : ℕ, ∃ n, m+1 ≤ n ∧ ∃ x ∈ K, ε ≤ dist (f x) (F n x) := by
    intro m
    have hh : ¬ (∀ n, m+1 ≤ n → ∀ x ∈ K, dist (f x) (F n x) < ε) := by
      intro hh
      exact hfail (eventually_atTop.mpr ⟨m+1,hh⟩)
    push Not at hh
    exact hh
  choose N hN x hx he using hbad
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun m ↦ (Nat.le_succ m).trans (hN m)) tendsto_id
  obtain ⟨s,hs,φ,hφ,hxs⟩ := hK.tendsto_subseq hx
  have hFt := hseq (N ∘ φ) (fun m ↦ by have := hN (φ m); simp only [Function.comp_apply]; omega)
    (hNt.comp hφ.tendsto_atTop) (x ∘ φ) (fun m ↦ hx (φ m)) s hs hxs
  have hfs := (hf s hs).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hxs,Eventually.of_forall (fun m ↦ hx (φ m))⟩)
  have hd := hfs.dist hFt
  simp only [dist_self] at hd
  have hzero : ε ≤ (0 : ℝ) := ge_of_tendsto hd
    (Eventually.of_forall (fun m ↦ he (φ m)))
  exact (not_le.mpr hε) hzero

end PerronWright.CompactSequentialUniform
