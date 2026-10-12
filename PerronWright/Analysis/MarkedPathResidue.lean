import PerronWright.Analysis.MarkedPathResolvent

/-!
# The diagonal residue identity for the marked-path pole

The marked-path pole constructed in `MarkedPathResolvent` has residue kernel
`Pi_g`.  This file proves the exact normalization used by the unicyclic
singularity:

`integral Pi_g(x,x) * partial_X T(g,0)(x) dmu(x) = -1`.

The proof differentiates the already constructed analytic eigenpair.  Kernel
symmetry supplies its genuine left eigenfunctional, so the derivative of the
eigenvector cancels.  No perturbative or spectral hypothesis is added.
-/

open MeasureTheory PerronWright
open scoped Topology ContDiff

noncomputable section

namespace PerronWright.MarkedPathResidue

namespace MPR

export PerronWright.MarkedPathResolvent
  (profile profile_analytic profile_base
   scalarIntegralCLM scalarIntegralCLM_apply
   eigenvalue eigenvalue_analytic eigenvector eigenvector_analytic
   pairingFunctional pairingFunctional_apply pairingNormalizer
   residueKernel residueKernel_analytic
   eigenpair_equations pathOperator_apply
   eigenvalueGap gapQuotient gapQuotient_analytic
   eigenvalueGap_eq_mul_gapQuotient eigenvalue_critical_axis
   pairingNormalizer_ne_zero gapQuotient_ne_zero poleKernel_apply)

end MPR

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private def verticalDirection : C(S, ℂ) × ℂ := (0, 1)

/-- The vertical derivative of the actual joint tree profile on the critical
axis. -/
def profileVertical (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℂ)) : C(S, ℂ) :=
  (fderiv ℂ (MPR.profile M hM) (g, 0)) verticalDirection

theorem profileVertical_analytic (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (profileVertical M hM) 0 := by
  have hf : AnalyticAt ℂ (fderiv ℂ (MPR.profile M hM)) (0, 0) :=
    (MPR.profile_analytic M hM).fderiv
  have hev : AnalyticAt ℂ
      (fun q : C(S, ℂ) × ℂ =>
        (fderiv ℂ (MPR.profile M hM) q) verticalDirection) (0, 0) := by
    exact ((ContinuousLinearMap.apply ℂ _ verticalDirection).analyticAt
      (fderiv ℂ (MPR.profile M hM) (0, 0))).comp_of_eq hf rfl
  exact hev.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl

private def diagonalMap : C(S, S × S) :=
  ⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩

private def diagonalRestrictionCLM : C(S × S, ℂ) →L[ℂ] C(S, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ diagonalMap

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
private theorem diagonalRestrictionCLM_apply (k : C(S × S, ℂ)) (x : S) :
    diagonalRestrictionCLM k x = k (x, x) :=
  rfl

/-- The diagonal pairing of the pole residue with the vertical profile
velocity. -/
def residueDiagonalPairing (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (g : C(S, ℂ)) : ℂ :=
  MPR.scalarIntegralCLM M
    (diagonalRestrictionCLM (MPR.residueKernel M hM g) *
      profileVertical M hM g)

theorem residueDiagonalPairing_analytic (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (residueDiagonalPairing M hM) 0 := by
  have hdiag : AnalyticAt ℂ
      (fun g => diagonalRestrictionCLM (MPR.residueKernel M hM g)) 0 :=
    ((diagonalRestrictionCLM (S := S)).analyticAt _).comp_of_eq
      (MPR.residueKernel_analytic M hM) rfl
  exact (MPR.scalarIntegralCLM M).analyticAt _ |>.comp
    (hdiag.mul (profileVertical_analytic M hM))

private theorem pairingFunctional_eigenvector (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (q : C(S, ℂ) × ℂ) :
    MPR.pairingFunctional M hM q (MPR.eigenvector M hM q) =
      MPR.pairingNormalizer M hM q := by
  rw [MPR.pairingFunctional_apply]
  unfold MPR.pairingNormalizer
  rw [MPR.scalarIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousMap.mul_apply]

/-- Symmetry turns the weighted right eigenvector into the actual left
eigenfunctional for the unweighted terminal kernel. -/
private theorem pairingFunctional_kernelAction (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), ∀ f : C(S, ℂ),
      MPR.pairingFunctional M hM q
          (M.kernel.complexAction M.mu f) =
        MPR.eigenvalue M hM q *
          MPR.scalarIntegralCLM M (MPR.eigenvector M hM q * f) := by
  filter_upwards [MPR.eigenpair_equations M hM] with q hq f
  let tau := MPR.profile M hM q
  let v := MPR.eigenvector M hM q
  let lam := MPR.eigenvalue M hM q
  calc
    MPR.pairingFunctional M hM q
          (M.kernel.complexAction M.mu f) =
        ∫ x, (tau * v) x * M.kernel.complexAction M.mu f x ∂M.mu := by
      rw [MPR.pairingFunctional_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [ContinuousMap.mul_apply, tau, v]
    _ = ∫ x, f x * M.kernel.complexAction M.mu (tau * v) x ∂M.mu :=
      TreeFoldUniformField.complexAction_pairing_symm M (tau * v) f
    _ = lam * MPR.scalarIntegralCLM M (v * f) := by
      rw [show M.kernel.complexAction M.mu (tau * v) = lam • v by
        simpa only [MPR.pathOperator_apply, tau, v, lam] using hq.1]
      rw [MPR.scalarIntegralCLM_apply, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply,
        smul_eq_mul]
      ring

/-- General simple-eigenvalue variation formula along the actual joint chart.
It is derived from the eigenpair equation and kernel symmetry, rather than
assumed as an additional perturbation interface. -/
theorem eigenvalue_fderiv_pairing (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), ∀ h : C(S, ℂ) × ℂ,
      (fderiv ℂ (MPR.eigenvalue M hM) q) h *
          MPR.pairingNormalizer M hM q =
        MPR.eigenvalue M hM q *
          MPR.scalarIntegralCLM M
            ((fderiv ℂ (MPR.profile M hM) q) h *
              MPR.eigenvector M hM q * MPR.eigenvector M hM q) := by
  let lhs : C(S, ℂ) × ℂ → C(S, ℂ) := fun q =>
    (M.kernel.complexActionCLM M.mu)
      ((MPR.profile M hM * MPR.eigenvector M hM) q)
  let rhs : C(S, ℂ) × ℂ → C(S, ℂ) :=
    MPR.eigenvalue M hM • MPR.eigenvector M hM
  have heq : lhs =ᶠ[𝓝 (0, 0)] rhs := by
    filter_upwards [MPR.eigenpair_equations M hM] with q hq
    simpa only [lhs, rhs, Pi.mul_apply, Pi.smul_apply, Pi.smul_apply',
      ContinuousKernel.complexActionCLM_apply, MPR.pathOperator_apply] using hq.1
  have hdeq : fderiv ℂ lhs =ᶠ[𝓝 (0, 0)] fderiv ℂ rhs :=
    heq.fderiv
  filter_upwards [hdeq,
    (MPR.profile_analytic M hM).eventually_analyticAt,
    (MPR.eigenvector_analytic M hM).eventually_analyticAt,
    (MPR.eigenvalue_analytic M hM).eventually_analyticAt,
    pairingFunctional_kernelAction M hM] with q hd hp hv hlam hkernel
  intro h
  have hleft : (fderiv ℂ lhs q) h =
      M.kernel.complexAction M.mu
        (MPR.profile M hM q *
            (fderiv ℂ (MPR.eigenvector M hM) q) h +
          MPR.eigenvector M hM q *
            (fderiv ℂ (MPR.profile M hM) q) h) := by
    have hprod := hp.differentiableAt.hasFDerivAt.mul
      hv.differentiableAt.hasFDerivAt
    have hcomp := (M.kernel.complexActionCLM M.mu).hasFDerivAt.comp q hprod
    have happ := congrArg (fun A => A h) hcomp.fderiv
    simpa only [lhs, Function.comp_def, ContinuousLinearMap.comp_apply,
      add_apply, smul_apply, ContinuousMap.smul_apply,
      smul_eq_mul, ContinuousKernel.complexActionCLM_apply] using happ
  have hright : (fderiv ℂ rhs q) h =
      (fderiv ℂ (MPR.eigenvalue M hM) q) h • MPR.eigenvector M hM q +
        MPR.eigenvalue M hM q •
          (fderiv ℂ (MPR.eigenvector M hM) q) h := by
    have hsmul := hlam.differentiableAt.hasFDerivAt.smul
      hv.differentiableAt.hasFDerivAt
    have happ := congrArg (fun A => A h) hsmul.fderiv
    simpa only [rhs, add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, Pi.smul_apply, add_comm] using happ
  have hdapp := congrArg (fun A => A h) hd
  rw [hleft, hright] at hdapp
  have hpaired := congrArg (MPR.pairingFunctional M hM q) hdapp
  rw [hkernel] at hpaired
  simp only [map_add, map_smul, smul_eq_mul] at hpaired
  rw [pairingFunctional_eigenvector M hM q] at hpaired
  have hpairDv :
      MPR.pairingFunctional M hM q
          ((fderiv ℂ (MPR.eigenvector M hM) q) h) =
        MPR.scalarIntegralCLM M
          (MPR.profile M hM q * MPR.eigenvector M hM q *
            (fderiv ℂ (MPR.eigenvector M hM) q) h) := by
    rw [MPR.pairingFunctional_apply, MPR.scalarIntegralCLM_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [ContinuousMap.mul_apply]
  rw [hpairDv] at hpaired
  have hintegral :
      MPR.scalarIntegralCLM M
          (MPR.eigenvector M hM q *
            (MPR.profile M hM q *
                (fderiv ℂ (MPR.eigenvector M hM) q) h +
              MPR.eigenvector M hM q *
                (fderiv ℂ (MPR.profile M hM) q) h)) =
        MPR.scalarIntegralCLM M
            ((fderiv ℂ (MPR.profile M hM) q) h *
              MPR.eigenvector M hM q * MPR.eigenvector M hM q) +
          MPR.scalarIntegralCLM M
            (MPR.profile M hM q * MPR.eigenvector M hM q *
              (fderiv ℂ (MPR.eigenvector M hM) q) h) := by
    rw [← map_add]
    congr 1
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply]
    ring
  rw [hintegral] at hpaired
  calc
    (fderiv ℂ (MPR.eigenvalue M hM) q) h *
          MPR.pairingNormalizer M hM q =
        ((fderiv ℂ (MPR.eigenvalue M hM) q) h *
            MPR.pairingNormalizer M hM q +
          MPR.eigenvalue M hM q *
            MPR.scalarIntegralCLM M
              (MPR.profile M hM q * MPR.eigenvector M hM q *
                (fderiv ℂ (MPR.eigenvector M hM) q) h)) -
          MPR.eigenvalue M hM q *
            MPR.scalarIntegralCLM M
              (MPR.profile M hM q * MPR.eigenvector M hM q *
                (fderiv ℂ (MPR.eigenvector M hM) q) h) := by ring
    _ = MPR.eigenvalue M hM q *
          (MPR.scalarIntegralCLM M
              ((fderiv ℂ (MPR.profile M hM) q) h *
                MPR.eigenvector M hM q * MPR.eigenvector M hM q) +
            MPR.scalarIntegralCLM M
              (MPR.profile M hM q * MPR.eigenvector M hM q *
                (fderiv ℂ (MPR.eigenvector M hM) q) h)) -
          MPR.eigenvalue M hM q *
            MPR.scalarIntegralCLM M
              (MPR.profile M hM q * MPR.eigenvector M hM q *
                (fderiv ℂ (MPR.eigenvector M hM) q) h) := by rw [← hpaired]
    _ = MPR.eigenvalue M hM q *
          MPR.scalarIntegralCLM M
            ((fderiv ℂ (MPR.profile M hM) q) h *
              MPR.eigenvector M hM q * MPR.eigenvector M hM q) := by ring

private theorem eigenvalue_vertical_eq_neg_gapQuotient
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      (fderiv ℂ (MPR.eigenvalue M hM) (g, 0)) verticalDirection =
        -MPR.gapQuotient M hM (g, 0) := by
  let gap : C(S, ℂ) × ℂ → ℂ := MPR.eigenvalueGap M hM
  let factored : C(S, ℂ) × ℂ → ℂ :=
    (fun q : C(S, ℂ) × ℂ => q.2) * MPR.gapQuotient M hM
  have heq : gap =ᶠ[𝓝 (0, 0)] factored := by
    filter_upwards [MPR.eigenvalueGap_eq_mul_gapQuotient M hM] with q hq
    simpa only [factored, Pi.mul_apply] using hq
  have hdeq : fderiv ℂ gap =ᶠ[𝓝 (0, 0)] fderiv ℂ factored :=
    heq.fderiv
  have haxis : Filter.Tendsto (fun g : C(S, ℂ) => (g, (0 : ℂ)))
      (𝓝 0) (𝓝 (0, 0)) :=
    (analyticAt_id.prod analyticAt_const : AnalyticAt ℂ
      (fun g : C(S, ℂ) => (g, (0 : ℂ))) 0).continuousAt.tendsto
  have hdaxis := haxis.eventually hdeq
  have hlamaxis := haxis.eventually
    (MPR.eigenvalue_analytic M hM).eventually_analyticAt
  have hQaxis := haxis.eventually
    (MPR.gapQuotient_analytic M hM).eventually_analyticAt
  filter_upwards [hdaxis, hlamaxis, hQaxis] with g hd hlam hQ
  have hdapp := congrArg (fun A => A verticalDirection) hd
  have hgap : (fderiv ℂ gap (g, 0)) verticalDirection =
      -(fderiv ℂ (MPR.eigenvalue M hM) (g, 0)) verticalDirection := by
    have hsub := hlam.differentiableAt.hasFDerivAt.const_sub (1 : ℂ)
    have happ := congrArg (fun A => A verticalDirection) hsub.fderiv
    change (fderiv ℂ
      (fun x : C(S, ℂ) × ℂ => 1 - MPR.eigenvalue M hM x) (g, 0))
        verticalDirection = _
    simpa only [neg_apply] using happ
  have hfactored : (fderiv ℂ factored (g, 0)) verticalDirection =
      MPR.gapQuotient M hM (g, 0) := by
    have hsnd : HasFDerivAt (fun q : C(S, ℂ) × ℂ => q.2)
        (ContinuousLinearMap.snd ℂ C(S, ℂ) ℂ) (g, 0) :=
      (ContinuousLinearMap.snd ℂ C(S, ℂ) ℂ).hasFDerivAt
    have hmul := hsnd.mul hQ.differentiableAt.hasFDerivAt
    have happ := congrArg (fun A => A verticalDirection) hmul.fderiv
    simpa only [factored, verticalDirection,
      add_apply, smul_apply, Prod.snd_zero, ContinuousLinearMap.coe_snd',
      smul_eq_mul, zero_mul, one_mul, mul_one, zero_add, add_zero] using happ
  rw [hgap, hfactored] at hdapp
  exact neg_eq_iff_eq_neg.mp hdapp

/-- Exact normalization of the marked-path residue on the critical axis.
This is the coefficient which produces the universal `-1/2 log X` term in
the unicyclic generating function. -/
theorem residue_diagonal_vertical_eq_neg_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      residueDiagonalPairing M hM g = -1 := by
  have haxis : Filter.Tendsto (fun g : C(S, ℂ) => (g, (0 : ℂ)))
      (𝓝 0) (𝓝 (0, 0)) :=
    (analyticAt_id.prod analyticAt_const : AnalyticAt ℂ
      (fun g : C(S, ℂ) => (g, (0 : ℂ))) 0).continuousAt.tendsto
  have hvariation := haxis.eventually (eigenvalue_fderiv_pairing M hM)
  have hlam := MPR.eigenvalue_critical_axis M hM
  have hdlam := eigenvalue_vertical_eq_neg_gapQuotient M hM
  have hN := haxis.eventually (MPR.pairingNormalizer_ne_zero M hM)
  have hQ := haxis.eventually (MPR.gapQuotient_ne_zero M hM)
  filter_upwards [hvariation, hlam, hdlam, hN, hQ] with g hvar hlam hdlam hN hQ
  have hvar' :
      (-MPR.gapQuotient M hM (g, 0)) *
          MPR.pairingNormalizer M hM (g, 0) =
        MPR.scalarIntegralCLM M
          (profileVertical M hM g * MPR.eigenvector M hM (g, 0) *
            MPR.eigenvector M hM (g, 0)) := by
    have h := hvar (verticalDirection (S := S))
    rw [hdlam, hlam, one_mul] at h
    simpa only [profileVertical] using h
  have hkernel :
      diagonalRestrictionCLM (MPR.residueKernel M hM g) *
          profileVertical M hM g =
        (MPR.eigenvalue M hM (g, 0) /
            (MPR.pairingNormalizer M hM (g, 0) *
              MPR.gapQuotient M hM (g, 0))) •
          (profileVertical M hM g * MPR.eigenvector M hM (g, 0) *
            MPR.eigenvector M hM (g, 0)) := by
    ext x
    simp only [diagonalRestrictionCLM_apply, MPR.residueKernel,
      MPR.poleKernel_apply, ContinuousMap.mul_apply,
      ContinuousMap.smul_apply, smul_eq_mul, profileVertical]
    ring
  rw [residueDiagonalPairing, hkernel, map_smul, smul_eq_mul, hlam, one_div]
  rw [← hvar']
  field_simp

end PerronWright.MarkedPathResidue
