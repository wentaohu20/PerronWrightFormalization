import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Analytic gluing on two open charts

This module isolates the elementary sheaf-style gluing step used by
the normalized Delta-domain construction.  Two analytic maps which agree on
the overlap of two open sets determine an analytic map on their union by a
set-theoretic piecewise definition.

The last two lemmas deliberately make no analytic assumptions: any
pointwise property, and in particular any residual equation, is inherited
from the two charts on their union.
-/

open scoped Classical

noncomputable section

namespace PerronWright.AnalyticTwoChartGluing

variable {E F G : Type*}

/-- Use `f` on the first chart and `g` off the first chart. -/
def glueOn (U : Set E) (f g : E → F) : E → F :=
  U.piecewise f g

/-- The glued map is definitionally the first chart on that chart. -/
theorem glueOn_eqOn_left (U : Set E) (f g : E → F) :
    Set.EqOn (glueOn U f g) f U := by
  exact Set.piecewise_eqOn U f g

/-- If the two charts agree on their overlap, the glued map is the second
chart throughout the second chart as well. -/
theorem glueOn_eqOn_right_of_eqOn_inter
    {U V : Set E} {f g : E → F}
    (hfg : Set.EqOn f g (U ∩ V)) :
    Set.EqOn (glueOn U f g) g V := by
  intro x hxV
  by_cases hxU : x ∈ U
  · rw [glueOn, Set.piecewise_eq_of_mem U f g hxU]
    exact hfg ⟨hxU, hxV⟩
  · exact Set.piecewise_eq_of_notMem U f g hxU

/-- Two analytic charts agreeing on their overlap glue to an analytic map on
their union. -/
theorem analyticOnNhd_glueOn_union
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U V : Set E} {f g : E → F}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g V)
    (hfg : Set.EqOn f g (U ∩ V)) :
    AnalyticOnNhd ℂ (glueOn U f g) (U ∪ V) := by
  have hleft : AnalyticOnNhd ℂ (glueOn U f g) U :=
    hf.congr hU (glueOn_eqOn_left U f g).symm
  have hright : AnalyticOnNhd ℂ (glueOn U f g) V :=
    hg.congr hV (glueOn_eqOn_right_of_eqOn_inter hfg).symm
  intro x hx
  rcases hx with hxU | hxV
  · exact hleft x hxU
  · exact hright x hxV

/-- A pointwise property inherited by both charts is inherited by their
piecewise gluing on the union.  No compatibility hypothesis is needed for
this purely pointwise assertion. -/
theorem glueOn_property_on_union
    {U V : Set E} {f g : E → F} {P : E → F → Prop}
    (hf : ∀ x ∈ U, P x (f x))
    (hg : ∀ x ∈ V, P x (g x)) :
    ∀ x ∈ U ∪ V, P x (glueOn U f g x) := by
  intro x hx
  by_cases hxU : x ∈ U
  · rw [glueOn, Set.piecewise_eq_of_mem U f g hxU]
    exact hf x hxU
  · have hxV : x ∈ V := hx.resolve_left hxU
    rw [glueOn, Set.piecewise_eq_of_notMem U f g hxU]
    exact hg x hxV

/-- The residual equation `R x y = 0` is inherited from the two charts on
their union. -/
theorem glueOn_residual_eq_zero_on_union
    [Zero G] {U V : Set E} {f g : E → F} {R : E → F → G}
    (hf : ∀ x ∈ U, R x (f x) = 0)
    (hg : ∀ x ∈ V, R x (g x) = 0) :
    ∀ x ∈ U ∪ V, R x (glueOn U f g x) = 0 := by
  exact glueOn_property_on_union
    (U := U) (V := V) (f := f) (g := g)
    (P := fun x y ↦ R x y = 0) hf hg

end PerronWright.AnalyticTwoChartGluing
