import PerronWright.Probability.GraphWindowMarkTransfer
import PerronWright.Probability.CountableWindowCountLimit

/-! # Actual localized TV profiles under changing empirical parameters

The bounded-parameter profile estimates apply to the actual graph laws
at a converging effective parameter. The exact whole-graph change of
parameter then gives profile control for the unnormalized source, under
the paper's actual critical-scale empirical spectral drift.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open CountableVariationMarks CountableComponentWindowLaw CountableTVWindowProfile
open GraphWindowMarkTransfer

variable (M : CountableKernel) (level : ℕ → ℕ)
variable {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
variable (p : VariationMark)
variable (hTV : ∀ R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
  ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
    ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
    (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
    M.growingDistanceLocalExpectation level lambda hlower hlo n y r p < ε)

include hTV in
theorem varying_windowBadEvent_probability_tendsto_zero
    (ell : ℕ → ℝ) (ellLimit : ℝ) (hell : Tendsto ell atTop (𝓝 ellLimit))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n ↦ (M.empiricalNormalizedGraphLaw level (ell n) hlower hlo n).real
      (badTVEvent (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) a b R p δ))
      atTop (𝓝 0) := by
  have hbnd : ∀ᶠ n in atTop, |ell n| ≤ |ellLimit| + 1 := by
    filter_upwards [hell.eventually (Icc_mem_nhds
      (a := ellLimit-1) (b := ellLimit+1) (by linarith) (by linarith))] with n hn
    apply abs_le.mpr
    constructor
    · linarith [hn.1, neg_abs_le ellLimit]
    · linarith [hn.2, le_abs_self ellLimit]
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ ↦ hc.trans_le measureReal_nonneg)
  · intro ε hε
    filter_upwards [hbnd, M.growing_windowBadProbability_zero_of_local_distance level p hlower hlo hTV
      a b (|ellLimit|+1) ha hab R δ hδ hε] with n hn he
    have hh := he (ell n) hn
    simpa only [growingWindowBadProbability, M.empiricalMarkedWindowLaw_badProbability_eq] using hh

include hTV in
theorem varying_windowDistance_tendsto_zero
    (ell : ℕ → ℝ) (ellLimit : ℝ) (hell : Tendsto ell atTop (𝓝 ellLimit))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Tendsto (fun n ↦ M.growingWindowDistanceExpectation level (ell n) a b R hlower hlo n p)
      atTop (𝓝 0) := by
  have hbnd : ∀ᶠ n in atTop, |ell n| ≤ |ellLimit| + 1 := by
    filter_upwards [hell.eventually (Icc_mem_nhds
      (a := ellLimit-1) (b := ellLimit+1) (by linarith) (by linarith))] with n hn
    apply abs_le.mpr
    constructor
    · linarith [hn.1, neg_abs_le ellLimit]
    · linarith [hn.2, le_abs_self ellLimit]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hbnd, M.growing_windowDistance_zero_of_local_distance level p hlower hlo hTV
    a b (|ellLimit|+1) ha hab R hε] with n hn he
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact he (ell n) hn
  · exact integral_nonneg (fun G ↦ windowDistance_nonneg _ G a b R p)

include hTV in
theorem unnormalized_windowBadEvent_probability_tendsto_zero
    (theta : ℝ)
    (hθ : Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
      (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta))
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n ↦ (M.empiricalUnnormalizedGraphLaw level lambda n).real
      (badTVEvent (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) a b R p δ))
      atTop (𝓝 0) := by
  have hh := M.varying_windowBadEvent_probability_tendsto_zero level hlower hlo p hTV
    (M.empiricalEffectiveParameter level lambda) (lambda+theta)
    (M.empiricalEffectiveParameter_tendsto level lambda theta hθ) a b ha hab R δ hδ
  simpa only [M.empiricalUnnormalizedGraphLaw_eq_effective_normalized level lambda hlower hlo] using hh

include hTV in
theorem unnormalized_windowDistance_tendsto_zero
    (theta : ℝ)
    (hθ : Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
      (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta))
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Tendsto (fun n ↦ ∫ G, windowDistance
      (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) G a b R p
      ∂M.empiricalUnnormalizedGraphLaw level lambda n) atTop (𝓝 0) := by
  have hh := M.varying_windowDistance_tendsto_zero level hlower hlo p hTV
    (M.empiricalEffectiveParameter level lambda) (lambda+theta)
    (M.empiricalEffectiveParameter_tendsto level lambda theta hθ) a b ha hab R
  simpa only [growingWindowDistanceExpectation,
    M.empiricalUnnormalizedGraphLaw_eq_effective_normalized level lambda hlower hlo] using hh

theorem graphMarkedWindowLaw_eq_empirical (lambda a b : ℝ) (R n : ℕ) :
    markedWindowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) a b R n =
      M.empiricalMarkedWindowLaw level lambda a b R hlower hlo n := rfl

theorem graphMarkedWindowLaw_eq_empiricalUnnormalized (lambda a b : ℝ) (R n : ℕ) :
    markedWindowLaw (M.empiricalUnnormalizedGraphLaw level lambda)
      (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) a b R n =
      M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R n := rfl

theorem empiricalUnnormalizedMarkedWindowLaw_badProbability_eq
    (lambda a b : ℝ) (R n : ℕ) (p : VariationMark) (δ : ℝ) :
    (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R n :
      Measure (FinitePointMeasureCompact.PointMeasure (MarkedWindow a b R))).real
        {η | 0 < FinitePointMeasureCompact.count η (badMarkCell a b R p δ)} =
      (M.empiricalUnnormalizedGraphLaw level lambda n).real
        (badTVEvent (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) a b R p δ) := by
  rw [measureReal_def, measureReal_def]
  change ((M.empiricalUnnormalizedGraphLaw level lambda n).map
    (fun G ↦ markedWindowPointMeasure
      (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) G a b R)
      {η | 0 < FinitePointMeasureCompact.count η (badMarkCell a b R p δ)}).toReal = _
  rw [Measure.map_apply (measurable_markedWindowPointMeasure _ a b R)
    (measurableSet_badPointEvent a b R p δ)]
  congr 1
  congr 1
  ext G
  exact (badTVEvent_iff_badPointCount _ G a b R p δ).symm

include hTV in
theorem unnormalized_markedWindowBadProbability_tendsto_zero
    (theta : ℝ)
    (hθ : Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
      (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta))
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n ↦ (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R n :
      Measure (FinitePointMeasureCompact.PointMeasure (MarkedWindow a b R))).real
        {η | 0 < FinitePointMeasureCompact.count η (badMarkCell a b R p δ)}) atTop (𝓝 0) := by
  simpa only [M.empiricalUnnormalizedMarkedWindowLaw_badProbability_eq] using
    M.unnormalized_windowBadEvent_probability_tendsto_zero level hlower hlo p hTV
      theta hθ lambda a b ha hab R δ hδ

end PerronWright.CountableKernel
