import PerronWright.Probability.FiniteIrreducibleFactorialDensityFloor

/-! # Uniform literal-density approximation with a varying scalar parameter

The actual density is jointly continuous in its scalar critical-window
parameter and its positive size tuple. Compactness and the finite bounded
surplus family turn scalar convergence into a uniform estimate. Combining
this estimate with the literal integer-floor estimate gives simultaneous
variation of the scalar parameter and the normalized size floors.
These are numerical statements, without a graph-law interface.
-/

open Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleVaryingDensity

open FiniteIrreducibleCriticalPrefactorScaling
open FiniteIrreducibleFactorialDensityFloor

theorem density_continuousOn_parameter_box (alpha beta : ℝ) {q : ℕ}
    (r : Fin q → ℕ) {a b c d : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun z : ℝ × (Fin q → ℝ) ↦ FactorialDensity.density alpha beta z.1 z.2 r)
      (Set.Icc c d ×ˢ Set.Icc (fun _ ↦ a) (fun _ ↦ b)) := by
  unfold FactorialDensity.density
  apply ContinuousOn.mul
  · have h : Continuous (fun z : ℝ × (Fin q → ℝ) ↦
        Real.exp (-FactorialDensity.criticalExponent alpha beta z.1 (∑ i, z.2 i))) := by
      unfold FactorialDensity.criticalExponent
      fun_prop
    exact h.continuousOn
  · apply continuousOn_finsetProd
    intro i _
    exact (FactorialDensity.sizeFactor_continuousOn_Icc beta (r i) ha).comp
      ((continuous_apply i).comp continuous_snd).continuousOn
      (fun z hz ↦ ⟨hz.2.1 i, hz.2.2 i⟩)

theorem density_uniformContinuousOn_parameter_box (alpha beta : ℝ) {q : ℕ}
    (r : Fin q → ℕ) {a b c d : ℝ} (ha : 0 < a) :
    UniformContinuousOn
      (fun z : ℝ × (Fin q → ℝ) ↦ FactorialDensity.density alpha beta z.1 z.2 r)
      (Set.Icc c d ×ˢ Set.Icc (fun _ ↦ a) (fun _ ↦ b)) :=
  (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (density_continuousOn_parameter_box alpha beta r ha)

theorem eventually_uniform_parameter_density_fixed_surplus
    (alpha beta : ℝ) (ell : ℕ → ℝ) (lambda : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) {q : ℕ} (r : Fin q → ℕ)
    (a b : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin q → ℝ,
      (∀ i, a ≤ x i) → (∀ i, x i ≤ b) →
      |FactorialDensity.density alpha beta (ell n) x r -
        FactorialDensity.density alpha beta lambda x r| < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (density_uniformContinuousOn_parameter_box alpha beta r
      (c := lambda - 1) (d := lambda + 1) ha) ε hε
  have hinterval : ∀ᶠ n in atTop, ell n ∈ Set.Icc (lambda - 1) (lambda + 1) :=
    hl.eventually (Icc_mem_nhds (by linarith) (by linarith))
  filter_upwards [hinterval, hl.eventually (Metric.ball_mem_nhds lambda hδ)]
    with n hn hdist x hxa hxb
  rw [← Real.dist_eq]
  exact hclose (ell n, x) ⟨hn, hxa, hxb⟩ (lambda, x)
    ⟨⟨by linarith, by linarith⟩, hxa, hxb⟩
    (by simpa only [dist_prod_same_right] using hdist)

/-- A single threshold controls all positive size tuples in the fixed box
and every bounded surplus tuple when the scalar parameter converges. -/
theorem eventually_uniform_parameter_density (alpha beta : ℝ)
    (ell : ℕ → ℝ) (lambda : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (q R : ℕ) (a b : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ x i) → (∀ i, x i ≤ b) → (∀ i, r i ≤ R) →
      |FactorialDensity.density alpha beta (ell n) x r -
        FactorialDensity.density alpha beta lambda x r| < ε := by
  have hfamily : ∀ r : Fin q → Fin (R+1), ∀ᶠ n : ℕ in atTop,
      ∀ x : Fin q → ℝ, (∀ i, a ≤ x i) → (∀ i, x i ≤ b) →
      |FactorialDensity.density alpha beta (ell n) x (fun i ↦ (r i : ℕ)) -
        FactorialDensity.density alpha beta lambda x (fun i ↦ (r i : ℕ))| < ε :=
    fun r ↦ eventually_uniform_parameter_density_fixed_surplus
      alpha beta ell lambda hl _ a b ha hε
  filter_upwards [eventually_all.mpr hfamily] with n hn x r hxa hxb hr
  exact hn (fun i ↦ ⟨r i, Nat.lt_succ_of_le (hr i)⟩) x hxa hxb

/-- The same uniform limit holds with the varying scalar parameter and the
actual integer floors simultaneously. -/
theorem eventually_uniform_varying_floor_density (alpha beta : ℝ)
    (ell : ℕ → ℝ) (lambda : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (q R : ℕ) (a b : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ x i) → (∀ i, x i ≤ b) → (∀ i, r i ≤ R) →
      |FactorialDensity.density alpha beta (ell n)
          (fun i ↦ normalizedSize n (CriticalScaling.size (x i) n)) r -
        FactorialDensity.density alpha beta lambda x r| < ε := by
  have hhalf : 0 < ε/2 := by linarith
  filter_upwards [eventually_floor_normalized_box q a b ha,
    eventually_uniform_parameter_density alpha beta ell lambda hl q R (a/2) b
      (by linarith) hhalf,
    eventually_uniform_floor_density alpha beta lambda q R a b ha hhalf]
    with n hbox hparameter hfloor x r hxa hxb hr
  let y : Fin q → ℝ := fun i ↦ normalizedSize n (CriticalScaling.size (x i) n)
  have hy : y ∈ Set.Icc (fun _ ↦ a/2) (fun _ ↦ b) := hbox x hxa hxb
  have hp := hparameter y r hy.1 hy.2 hr
  have hf := hfloor x r hxa hxb hr
  calc
    |FactorialDensity.density alpha beta (ell n) y r -
        FactorialDensity.density alpha beta lambda x r| ≤
        |FactorialDensity.density alpha beta (ell n) y r -
          FactorialDensity.density alpha beta lambda y r| +
        |FactorialDensity.density alpha beta lambda y r -
          FactorialDensity.density alpha beta lambda x r| := abs_sub_le _ _ _
    _ < ε := by dsimp [y] at hp ⊢; linarith

end PerronWright.FiniteIrreducibleVaryingDensity
