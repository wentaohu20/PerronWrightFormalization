import PerronWright.Analysis.FiniteIrreducibleFieldTreeGlobalDissymmetry
import PerronWright.Analysis.TreeFoldJointDivision
import PerronWright.Analysis.FiniteIrreducibleZeroFieldTreeIntegratedSingularity

/-!
# The joint field-tree fold expansion

The canonical joint fold profile is already analytic in the field and fold
coordinates and solves the genuine tree equation at activity
`rho(g) * (1 - X^2)`.  Applying the tree dissymmetry functional gives an
analytic scalar germ.  This file proves, rather than assumes, its joint
cubic expansion

`C(g) + A2(g) X^2 + A3(g) X^3 + X^4 R(g,X)`.

The vanishing of the linear term follows from the rooting derivative and the
fact that `rho(g) * (1 - X^2)` has zero derivative at `X = 0`.  The remaining
factors are obtained by the analytic vertical-division theorem.  The values
`A2(0) = -1` and `A3(0) = 2 gamma / 3` are identified from the previously
proved zero-field analytic primitive, not installed as new assumptions.

In the global normalized activity coordinate, this germ is the continuation
of `G(1 - X^2,g)` on the chosen square-root sheet.  Keeping the statement in
the genuine fold coordinate avoids asserting the false identity
`sqrt(1-X^2) = X` simultaneously on both sides of the slit.
-/

open Filter Topology Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleFieldTreeJointFoldExpansion

namespace GC

export PerronWright.ZeroFieldTreeGlobalContinuation (treeDissymmetryFunctional)
export PerronWright.FiniteIrreducibleTreeDissymmetry
  (zeroFieldFoldDissymmetry exists_zeroFieldFoldDissymmetry_derivative)

end GC

namespace MPR

export PerronWright.FiniteIrreducibleMarkedPathResolvent
  (scalarIntegralCLM)

end MPR

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The unrooted-tree dissymmetry functional in the genuine joint fold
coordinates `(g,X)`. -/
def jointFoldTreeFunction (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  GC.treeDissymmetryFunctional M.bjrModel
    (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM q)

theorem jointFoldTreeFunction_analyticAt (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (jointFoldTreeFunction M hM) (0, 0) := by
  exact
    FieldTreeGlobalDissymmetry.treeDissymmetryFunctional_analyticAt_comp M.bjrModel
      (FiniteIrreducibleNormalizedFoldActivity.foldProfile_analytic M hM)

@[simp] theorem jointFoldTreeFunction_zeroField
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (X : ℂ) :
    jointFoldTreeFunction M hM (0, X) =
      GC.zeroFieldFoldDissymmetry M hM X := rfl

/-- For every sufficiently small complex field, the fold-coordinate
derivative of the dissymmetry functional vanishes at the fold point.  This
is the field-dependent rooting identity with
`z(X) = rho(g) * (1-X^2)`. -/
theorem jointFoldTreeFunction_vertical_deriv_zero
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      deriv (fun X : ℂ ↦ jointFoldTreeFunction M hM (g, X)) 0 = 0 := by
  have hgood : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      AnalyticAt ℂ (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM) q ∧
        TreeCritical.residual M.bjrModel
          ((FiniteIrreducibleRadiusResponse.radius M hM q.1 * (1 - q.2 ^ 2), q.1),
            FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM q) = 0 :=
    (FiniteIrreducibleNormalizedFoldActivity.foldProfile_analytic M hM).eventually_analyticAt.and
      (by simpa only [FiniteIrreducibleModel.treeResidual] using
        FiniteIrreducibleNormalizedFoldActivity.foldProfile_residual M hM)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hrho : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      FiniteIrreducibleRadiusResponse.radius M hM g ≠ 0 :=
    (FiniteIrreducibleRadiusResponse.radius_analytic M hM).continuousAt.eventually_ne (by
      rw [FiniteIrreducibleRadiusResponse.radius_base]
      exact one_ne_zero)
  filter_upwards [Metric.ball_mem_nhds (0 : C(S, ℂ)) hr, hrho] with g hg hrg
  let rho : ℂ := FiniteIrreducibleRadiusResponse.radius M hM g
  let z : ℂ → ℂ := fun X ↦ rho * (1 - X ^ 2)
  let T : ℂ → C(S, ℂ) := fun X ↦
    FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (g, X)
  have hp0 : (g, (0 : ℂ)) ∈
      Metric.ball (0 : C(S, ℂ) × ℂ) r := by
    rw [← ball_prod_same]
    exact ⟨hg, Metric.mem_ball_self hr⟩
  have hTa : AnalyticAt ℂ T 0 := by
    exact (hball hp0).1.comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl
  have hfix : ∀ᶠ X : ℂ in 𝓝 0,
      T X = z X • NormedSpace.exp
        (g - TreeCritical.degree M.bjrModel +
          M.bjrModel.kernel.complexActionCLM M.bjrModel.mu (T X)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with X hX
    have hp : (g, X) ∈ Metric.ball (0 : C(S, ℂ) × ℂ) r := by
      rw [← ball_prod_same]
      exact ⟨hg, hX⟩
    have hres := (hball hp).2
    change T X - z X • NormedSpace.exp
      (g - TreeCritical.degree M.bjrModel +
        M.bjrModel.kernel.complexActionCLM M.bjrModel.mu (T X)) = 0 at hres
    exact sub_eq_zero.mp hres
  have hinner : HasDerivAt (fun X : ℂ ↦ 1 - X ^ 2) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℂ)).const_sub (1 : ℂ))
  have hz : HasDerivAt z 0 0 := by
    simpa only [z, mul_zero] using hinner.const_mul rho
  have hzne : z 0 ≠ 0 := by
    simpa only [z, pow_two, zero_mul, sub_zero, mul_one, rho] using hrg
  have hformula :=
    FieldTreeGlobalDissymmetry.treeDissymmetryFunctional_hasDerivAt_of_fieldFixedPoint
      M.bjrModel g hz hTa.differentiableAt.hasDerivAt hfix hzne
  change deriv (fun X : ℂ ↦
    GC.treeDissymmetryFunctional M.bjrModel (T X)) 0 = 0
  rw [hformula.deriv]
  simp

/-- The zero-field slice of the joint fold germ, after subtracting its value
at the fold point, has the already established normalized cubic expansion. -/
theorem exists_jointFoldTreeFunction_zeroField_expansion
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ R₀ : ℂ → ℂ, AnalyticAt ℂ R₀ 0 ∧
      ∀ᶠ X : ℂ in 𝓝 0,
        jointFoldTreeFunction M hM (0, X) -
            jointFoldTreeFunction M hM (0, 0) =
          -X ^ 2 +
            (2 * (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3 +
              X ^ 4 * R₀ X := by
  obtain ⟨U, R₀, rU, hrU, hU0, hUa, hR₀a, hUderiv, hUexp⟩ :=
    FiniteIrreducibleZeroFieldTreeIntegratedSingularity.exists_normalized_zeroFieldTree_fold_expansion
      M hM
  obtain ⟨rF, hrF, hFa, hFderiv⟩ :=
    GC.exists_zeroFieldFoldDissymmetry_derivative M hM
  let r : ℝ := min rF rU
  have hr : 0 < r := lt_min hrF hrU
  have hrF' : r ≤ rF := min_le_left rF rU
  have hrU' : r ≤ rU := min_le_right rF rU
  let F₀ : ℂ → ℂ := fun X ↦ GC.zeroFieldFoldDissymmetry M hM X
  have hF₀a : AnalyticOnNhd ℂ F₀ (Metric.ball (0 : ℂ) r) := by
    exact hFa.mono (Metric.ball_subset_ball hrF')
  have hCUa : AnalyticOnNhd ℂ (fun X : ℂ ↦ F₀ 0 + U X)
      (Metric.ball (0 : ℂ) r) := by
    exact analyticOnNhd_const.add
      (hUa.mono (Metric.ball_subset_ball hrU'))
  have hderivEq : Set.EqOn (deriv F₀)
      (deriv (fun X : ℂ ↦ F₀ 0 + U X))
      (Metric.ball (0 : ℂ) r) := by
    intro X hX
    have hF := hFderiv X (Metric.ball_subset_ball hrF' hX)
    have hU := (hUderiv X
      (Metric.ball_subset_ball hrU' hX)).const_add (F₀ 0)
    exact hF.deriv.trans hU.deriv.symm
  have hEq : Set.EqOn F₀ (fun X : ℂ ↦ F₀ 0 + U X)
      (Metric.ball (0 : ℂ) r) :=
    Metric.isOpen_ball.eqOn_of_deriv_eq
      (convex_ball (0 : ℂ) r).isPreconnected
      hF₀a.differentiableOn hCUa.differentiableOn hderivEq
      (Metric.mem_ball_self hr) (by simp [hU0])
  have hEqNear : ∀ᶠ X : ℂ in 𝓝 0,
      F₀ X - F₀ 0 = U X := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with X hX
    rw [hEq hX]
    ring
  refine ⟨R₀, hR₀a, ?_⟩
  filter_upwards [hEqNear, hUexp] with X hEqX hUX
  simpa only [jointFoldTreeFunction_zeroField, F₀] using hEqX.trans hUX

/-- The canonical field-tree fold germ has a jointly analytic cubic
expansion.  `C`, `A₂`, and `A₃` are analytic field germs, while `R` is
analytic jointly in `(g,X)`.  The two universal zero-field coefficients are
fixed by the genuine zero-field tree singularity. -/
theorem exists_jointFoldTreeFunction_cubic_expansion
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (C A₂ A₃ : C(S, ℂ) → ℂ) (R : C(S, ℂ) × ℂ → ℂ),
      AnalyticAt ℂ C 0 ∧ AnalyticAt ℂ A₂ 0 ∧
      AnalyticAt ℂ A₃ 0 ∧ AnalyticAt ℂ R (0, 0) ∧
      A₂ 0 = -1 ∧
      A₃ 0 = 2 * (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) / 3 ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        jointFoldTreeFunction M hM q =
          C q.1 + A₂ q.1 * q.2 ^ 2 + A₃ q.1 * q.2 ^ 3 +
            q.2 ^ 4 * R q := by
  let F : C(S, ℂ) × ℂ → ℂ := jointFoldTreeFunction M hM
  let C : C(S, ℂ) → ℂ := fun g ↦ F (g, 0)
  let Fₒ : C(S, ℂ) × ℂ → ℂ := fun q ↦ F q - C q.1
  have hFa : AnalyticAt ℂ F (0, 0) :=
    jointFoldTreeFunction_analyticAt M hM
  have hCa : AnalyticAt ℂ C 0 := by
    exact hFa.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  have hFₒa : AnalyticAt ℂ Fₒ (0, 0) := by
    exact hFa.sub (hCa.comp_of_eq analyticAt_fst rfl)
  have hFₒ0 : ∀ᶠ g : C(S, ℂ) in 𝓝 0, Fₒ (g, 0) = 0 := by
    exact Filter.Eventually.of_forall (by intro g; simp [Fₒ, C])
  have hemb : Tendsto (fun g : C(S, ℂ) ↦ (g, (0 : ℂ)))
      (𝓝 0) (𝓝 (0, 0)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hFnear : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      AnalyticAt ℂ F q := hFa.eventually_analyticAt
  have hFₒd : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      deriv (fun X : ℂ ↦ Fₒ (g, X)) 0 = 0 := by
    filter_upwards [jointFoldTreeFunction_vertical_deriv_zero M hM,
      hemb.eventually hFnear] with g hzero hgA
    have hslice : AnalyticAt ℂ (fun X : ℂ ↦ F (g, X)) 0 :=
      hgA.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    have hcentered : HasDerivAt (fun X : ℂ ↦ Fₒ (g, X))
        (deriv (fun X : ℂ ↦ F (g, X)) 0) 0 := by
      simpa only [Fₒ, C] using
        hslice.differentiableAt.hasDerivAt.sub_const (F (g, 0))
    exact hcentered.deriv.trans hzero
  obtain ⟨H, hHa, hquadratic⟩ :=
    TreeFoldJointDivision.analytic_vertical_second_division
      hFₒa hFₒ0 hFₒd
  let A₂ : C(S, ℂ) → ℂ := fun g ↦ H (g, 0)
  let H₁ : C(S, ℂ) × ℂ → ℂ := fun q ↦ H q - A₂ q.1
  have hA₂a : AnalyticAt ℂ A₂ 0 := by
    exact hHa.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  have hH₁a : AnalyticAt ℂ H₁ (0, 0) := by
    exact hHa.sub (hA₂a.comp_of_eq analyticAt_fst rfl)
  have hH₁0 : ∀ᶠ g : C(S, ℂ) in 𝓝 0, H₁ (g, 0) = 0 := by
    exact Filter.Eventually.of_forall (by intro g; simp [H₁, A₂])
  obtain ⟨Q, hQa, hcubic⟩ :=
    TreeFoldJointDivision.analytic_vertical_division hH₁a hH₁0
  let A₃ : C(S, ℂ) → ℂ := fun g ↦ Q (g, 0)
  let Q₁ : C(S, ℂ) × ℂ → ℂ := fun q ↦ Q q - A₃ q.1
  have hA₃a : AnalyticAt ℂ A₃ 0 := by
    exact hQa.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  have hQ₁a : AnalyticAt ℂ Q₁ (0, 0) := by
    exact hQa.sub (hA₃a.comp_of_eq analyticAt_fst rfl)
  have hQ₁0 : ∀ᶠ g : C(S, ℂ) in 𝓝 0, Q₁ (g, 0) = 0 := by
    exact Filter.Eventually.of_forall (by intro g; simp [Q₁, A₃])
  obtain ⟨R, hRa, hquartic⟩ :=
    TreeFoldJointDivision.analytic_vertical_division hQ₁a hQ₁0

  obtain ⟨R₀, hR₀a, hzeroExpansion⟩ :=
    exists_jointFoldTreeFunction_zeroField_expansion M hM
  let c₃ : ℂ := 2 * (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) / 3
  let K₂ : ℂ → ℂ := fun X ↦ -1 + c₃ * X + X ^ 2 * R₀ X
  let K₃ : ℂ → ℂ := fun X ↦ c₃ + X * R₀ X
  have hsection : Tendsto (fun X : ℂ ↦ ((0 : C(S, ℂ)), X))
      (𝓝 0) (𝓝 (0, 0)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hquadratic₀ : ∀ᶠ X : ℂ in 𝓝 0,
      Fₒ (0, X) = X ^ 2 * H (0, X) := by
    simpa using hsection.eventually hquadratic
  have hcubic₀ : ∀ᶠ X : ℂ in 𝓝 0,
      H₁ (0, X) = X * Q (0, X) := by
    simpa using hsection.eventually hcubic
  have hK₂a : AnalyticAt ℂ K₂ 0 := by
    dsimp only [K₂]
    fun_prop
  have hK₃a : AnalyticAt ℂ K₃ 0 := by
    dsimp only [K₃]
    fun_prop
  have hHK₂ : ∀ᶠ X : ℂ in 𝓝[≠] 0, H (0, X) = K₂ X := by
    filter_upwards [hquadratic₀.filter_mono nhdsWithin_le_nhds,
      hzeroExpansion.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with X hquad hzero hX
    have hmul : X ^ 2 * H (0, X) = X ^ 2 * K₂ X := by
      rw [← hquad]
      change jointFoldTreeFunction M hM (0, X) -
          jointFoldTreeFunction M hM (0, 0) = _
      rw [hzero]
      dsimp only [K₂, c₃]
      ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hX) hmul
  have hHslice : AnalyticAt ℂ (fun X : ℂ ↦ H (0, X)) 0 :=
    hHa.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hH₀ : H (0, 0) = K₂ 0 :=
    tendsto_nhds_unique_of_eventuallyEq
      (hHslice.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hK₂a.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hHK₂
  have hA₂0 : A₂ 0 = -1 := by
    change H (0, 0) = -1
    rw [hH₀]
    simp [K₂]
  have hQK₃ : ∀ᶠ X : ℂ in 𝓝[≠] 0, Q (0, X) = K₃ X := by
    filter_upwards [hcubic₀.filter_mono nhdsWithin_le_nhds,
      hHK₂, self_mem_nhdsWithin] with X hcub hHK hX
    have hmul : X * Q (0, X) = X * K₃ X := by
      rw [← hcub]
      change H (0, X) - A₂ 0 = _
      rw [hHK, hA₂0]
      dsimp only [K₂, K₃]
      ring
    exact mul_left_cancel₀ hX hmul
  have hQslice : AnalyticAt ℂ (fun X : ℂ ↦ Q (0, X)) 0 :=
    hQa.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hQ₀ : Q (0, 0) = K₃ 0 :=
    tendsto_nhds_unique_of_eventuallyEq
      (hQslice.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hK₃a.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hQK₃
  have hA₃0 : A₃ 0 = c₃ := by
    change Q (0, 0) = c₃
    rw [hQ₀]
    simp [K₃]

  refine ⟨C, A₂, A₃, R, hCa, hA₂a, hA₃a, hRa,
    hA₂0, ?_, ?_⟩
  · simpa only [c₃] using hA₃0
  · filter_upwards [hquadratic, hcubic, hquartic] with q hquad hcub hquart
    dsimp only [Fₒ, H₁, Q₁] at hquad hcub hquart
    change F q = C q.1 + A₂ q.1 * q.2 ^ 2 +
      A₃ q.1 * q.2 ^ 3 + q.2 ^ 4 * R q
    rw [show F q = C q.1 + q.2 ^ 2 * H q by
      exact (sub_eq_iff_eq_add.mp hquad).trans (add_comm _ _)]
    rw [show H q = A₂ q.1 + q.2 * Q q by
      exact (sub_eq_iff_eq_add.mp hcub).trans (add_comm _ _)]
    rw [show Q q = A₃ q.1 + q.2 * R q by
      exact (sub_eq_iff_eq_add.mp hquart).trans (add_comm _ _)]
    ring

end PerronWright.FiniteIrreducibleFieldTreeJointFoldExpansion
