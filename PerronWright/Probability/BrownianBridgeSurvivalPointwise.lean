import PerronWright.Probability.BrownianFirstPassageBridgeLaw
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Pointwise identification of actual bridge survival probabilities

The actual pinned-bridge constraint is monotone in the endpoint. Hence
an almost-everywhere formula with a continuous right-hand side identifies
the probability at every endpoint, not merely a Gaussian-a.e. version.
This file proves that upgrade; it does not assume a reflection or killed
transition formula for the bridge probability.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
noncomputable section

namespace PerronWright.BrownianBridgeSurvivalPointwise

theorem monotone_eq_of_dense_eq {Y : Type*} [LinearOrder Y]
    [TopologicalSpace Y] [OrderClosedTopology Y]
    {f g : ℝ → Y} (hf : Monotone f) (hg : Continuous g)
    (hd : Dense {x | f x = g x}) : f = g := by
  funext x
  apply le_antisymm
  · have hC : IsClosed {y | f x ≤ g y} := isClosed_le continuous_const hg
    have hs : Ioi x ∩ {y | f y = g y} ⊆ {y | f x ≤ g y} := by
      intro y hy
      change f x ≤ g y
      rw [← hy.2]
      exact hf hy.1.le
    have hi : Ioi x ⊆ {y | f x ≤ g y} :=
      (hd.open_subset_closure_inter isOpen_Ioi).trans
        (hC.closure_subset_iff.mpr hs)
    exact (hC.closure_subset_iff.mpr hi) (by
      simpa only [closure_Ioi] using (show x ∈ Ici x by exact mem_Ici.mpr le_rfl))
  · have hC : IsClosed {y | g y ≤ f x} := isClosed_le hg continuous_const
    have hs : Iio x ∩ {y | f y = g y} ⊆ {y | g y ≤ f x} := by
      intro y hy
      change g y ≤ f x
      rw [← hy.2]
      exact hf hy.1.le
    have hi : Iio x ⊆ {y | g y ≤ f x} :=
      (hd.open_subset_closure_inter isOpen_Iio).trans
        (hC.closure_subset_iff.mpr hs)
    exact (hC.closure_subset_iff.mpr hi) (by
      simpa only [closure_Iio] using (show x ∈ Iic x by exact mem_Iic.mpr le_rfl))

theorem monotone_eq_of_ae_eq {Y : Type*} [LinearOrder Y]
    [TopologicalSpace Y] [OrderClosedTopology Y]
    (μ : Measure ℝ) [μ.IsOpenPosMeasure] {f g : ℝ → Y}
    (hf : Monotone f) (hg : Continuous g) (hfg : f =ᵐ[μ] g) : f = g :=
  monotone_eq_of_dense_eq hf hg (μ.dense_of_ae hfg)

open BrownianPathLaw BrownianFirstPassageBridgeLaw

theorem bridgeConstraint_subset_of_le (level : ℝ) (T : ℝ≥0)
    {z z' : ℝ} (hzz' : z ≤ z') :
    bridgeConstraint level T z ⊆ bridgeConstraint level T z' := by
  intro f hf
  rw [mem_bridgeConstraint_iff] at hf ⊢
  intro t ht
  exact (hf t ht).trans_le (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hzz' (div_nonneg t.coe_nonneg T.coe_nonneg)))

theorem monotone_bridgeConstraint_probability (level : ℝ) (T : ℝ≥0) :
    Monotone (fun z : ℝ ↦ pinnedLaw T (bridgeConstraint level T z)) := by
  intro z z' hzz'
  exact measure_mono (bridgeConstraint_subset_of_le level T hzz')

theorem bridgeConstraint_probability_eq_of_gaussian_ae
    (level : ℝ) (T : ℝ≥0) (hT : 0 < T) (m : ℝ)
    {G : ℝ → ℝ≥0∞} (hG : Continuous G)
    (h : (fun z : ℝ ↦ pinnedLaw T (bridgeConstraint level T z)) =ᵐ[gaussianReal m T] G) :
    (fun z : ℝ ↦ pinnedLaw T (bridgeConstraint level T z)) = G := by
  have : (gaussianReal m T).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' m (ne_of_gt hT)).isOpenPosMeasure
  exact monotone_eq_of_ae_eq (gaussianReal m T)
    (monotone_bridgeConstraint_probability level T) hG h

end PerronWright.BrownianBridgeSurvivalPointwise
