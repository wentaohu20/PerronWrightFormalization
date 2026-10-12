import PerronWright.Analysis.RootedTreeUnitJointField
import PerronWright.Analysis.TreeFoldPhysicalGluing
import PerronWright.Enumeration.RootedTreeSeriesPhysical

/-!
# Joint uniqueness on analytic tree-solution overlaps

This module isolates the analytic-uniqueness step needed when the unit-away
tree continuation is glued to the local fold chart.  It does not infer joint
equality from equality on the zero-field slice.  Instead, the actual physical
solution at one real subcritical point supplies an implicit-function
uniqueness neighborhood; equality on that genuinely open joint neighborhood
then propagates through the whole preconnected overlap by analytic
continuation.

The theorem below assumes that the two analytic solutions and their open
preconnected overlap have already been constructed.  In particular, it does
not construct the selected square-root sheet which converts the fold chart
from `(g,X)` coordinates to `(z,g)` coordinates, nor does it assert the
geometric existence of the required overlap with the unit-away domain.
-/

open Filter Topology
open scoped Classical

noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- Two analytic solutions agree on an open preconnected overlap once one
solution retains a genuine local residual-uniqueness neighborhood at an
arbitrary complex seed where the two values coincide. -/
theorem analytic_solutions_agree_on_open_preconnected_overlap_of_local_uniqueness
    (R : ((ℂ × C(S, ℂ)) × C(S, ℂ)) → C(S, ℂ))
    (U : Set (ℂ × C(S, ℂ))) (hUopen : IsOpen U)
    (hUpre : IsPreconnected U)
    (Ψ₁ Ψ₂ : ℂ × C(S, ℂ) → C(S, ℂ))
    (h₁a : AnalyticOnNhd ℂ Ψ₁ U)
    (h₂a : AnalyticOnNhd ℂ Ψ₂ U)
    (h₂res : ∀ q ∈ U, R (q, Ψ₂ q) = 0)
    (q₀ : ℂ × C(S, ℂ)) (hq₀ : q₀ ∈ U)
    (hseed : Ψ₁ q₀ = Ψ₂ q₀)
    (h₁uniq : ∀ᶠ p in nhds (q₀, Ψ₁ q₀),
      R p = 0 ↔ Ψ₁ p.1 = p.2) :
    Set.EqOn Ψ₁ Ψ₂ U := by
  have hgraph₂ : Tendsto (fun q => (q, Ψ₂ q)) (nhds q₀)
      (nhds (q₀, Ψ₁ q₀)) := by
    have h := tendsto_id.prodMk_nhds (h₂a q₀ hq₀).continuousAt.tendsto
    simpa only [id_eq, hseed] using h
  have hUnhd : U ∈ nhds q₀ := hUopen.mem_nhds hq₀
  have heqNhd : Ψ₁ =ᶠ[nhds q₀] Ψ₂ := by
    filter_upwards [hgraph₂.eventually h₁uniq, hUnhd]
      with q hlocal hqU
    exact hlocal.mp (h₂res q hqU)
  exact h₁a.eqOn_of_preconnected_of_eventuallyEq h₂a hUpre hq₀ heqNhd

variable [MeasurableSpace S] [BorelSpace S]

/-- Two jointly analytic solutions of the genuine compact-BJR tree equation
agree on an open preconnected overlap if they both meet the actual rooted-tree
series at one real subcritical point of that overlap.

Equality at the seed is first upgraded to equality on a genuinely open joint
neighborhood by the implicit-function uniqueness of the physical solution.
Analytic continuation then propagates that equality through the whole
preconnected overlap. -/
theorem CompactBJRModel.joint_tree_solutions_agree_on_open_preconnected_overlap
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (U : Set (ℂ × C(S, ℂ))) (hUopen : IsOpen U)
    (hUpre : IsPreconnected U)
    (Ψ₁ Ψ₂ : ℂ × C(S, ℂ) → C(S, ℂ))
    (h₁a : AnalyticOnNhd ℂ Ψ₁ U)
    (h₂a : AnalyticOnNhd ℂ Ψ₂ U)
    (h₁res : ∀ q ∈ U, TreeCritical.residual M (q, Ψ₁ q) = 0)
    (h₂res : ∀ q ∈ U, TreeCritical.residual M (q, Ψ₂ q) = 0)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1)
    (hseedMem : ((w : ℂ), (0 : C(S, ℂ))) ∈ U)
    (h₁seed : Ψ₁ ((w : ℂ), 0) = M.rootedTreeSeries (w : ℂ))
    (h₂seed : Ψ₂ ((w : ℂ), 0) = M.rootedTreeSeries (w : ℂ)) :
    Set.EqOn Ψ₁ Ψ₂ U := by
  obtain ⟨V, -, hVbounds, hVfix, hseries⟩ :=
    M.rootedTreeSeries_eq_physical_fixedPoint hM w hw hw1
  obtain ⟨ψ, -, -, -, huniq⟩ :=
    TreeSubcriticalAnalytic.physicalTree_subcritical_analytic_neighborhood
      M hM w hw hw1 V hVbounds hVfix
  let q₀ : ℂ × C(S, ℂ) := ((w : ℂ), 0)
  let T₀ : C(S, ℂ) := TreeRealComplexBridge.complexify V
  have hq₀U : q₀ ∈ U := hseedMem
  have h₁base : Ψ₁ q₀ = T₀ := h₁seed.trans hseries
  have h₂base : Ψ₂ q₀ = T₀ := h₂seed.trans hseries
  have h₁graph : Tendsto (fun q => (q, Ψ₁ q)) (𝓝 q₀) (𝓝 (q₀, T₀)) := by
    have h := tendsto_id.prodMk_nhds (h₁a q₀ hq₀U).continuousAt.tendsto
    simpa only [id_eq, h₁base] using h
  have h₂graph : Tendsto (fun q => (q, Ψ₂ q)) (𝓝 q₀) (𝓝 (q₀, T₀)) := by
    have h := tendsto_id.prodMk_nhds (h₂a q₀ hq₀U).continuousAt.tendsto
    simpa only [id_eq, h₂base] using h
  have huniq' :
      ∀ᶠ p in 𝓝 (q₀, T₀),
        TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2 := by
    simpa only [q₀, T₀] using huniq
  have hUnhd : U ∈ 𝓝 q₀ := hUopen.mem_nhds hq₀U
  have h₁eq : Ψ₁ =ᶠ[𝓝 q₀] ψ := by
    filter_upwards [h₁graph.eventually huniq', hUnhd] with q hlocal hqU
    exact (hlocal.mp (h₁res q hqU)).symm
  have h₂eq : Ψ₂ =ᶠ[𝓝 q₀] ψ := by
    filter_upwards [h₂graph.eventually huniq', hUnhd] with q hlocal hqU
    exact (hlocal.mp (h₂res q hqU)).symm
  have h₁₂ : Ψ₁ =ᶠ[𝓝 q₀] Ψ₂ := h₁eq.trans h₂eq.symm
  exact h₁a.eqOn_of_preconnected_of_eventuallyEq h₂a hUpre hq₀U h₁₂

end PerronWright
