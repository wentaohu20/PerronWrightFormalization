import PerronWright.Enumeration.MarkedPathOperatorPower
import PerronWright.Analysis.FiniteIrreducibleNormalizedFoldActivity
import PerronWright.Analysis.FiniteIrreducibleUniformFieldFold
import PerronWright.Analysis.FiniteIrreducibleAugmented
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Ring.Units
import PerronWright.Analysis.AnalyticVerticalDivision

/-!
# Actual marked-path resolvent for the finite irreducible fold

This module constructs the operator-theoretic layer needed after the literal
path/operator-power identity.  It uses the actual joint fold chart, the
analytic Perron eigenpair, and the augmented inverse at the base profile to
derive the rank-one pole and its jointly analytic remainder.  No spectral or
resolvent hypothesis is added. Only literal matrix criticality is required;
negative unit eigenvalues and bipartite kernels remain admissible.
-/

open MeasureTheory PerronWright
open scoped Topology ContDiff

noncomputable section

namespace PerronWright.FiniteIrreducibleMarkedPathResolvent

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]


/-- Canonical actual joint tree profile in square-root coordinates. -/
def profile (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    C(S, ℂ) × ℂ → C(S, ℂ) :=
  FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM

theorem profile_analytic (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℂ (profile M hM) (0, 0) :=
  FiniteIrreducibleNormalizedFoldActivity.foldProfile_analytic M hM

theorem profile_base (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    profile M hM (0, 0) = 1 :=
  FiniteIrreducibleNormalizedFoldActivity.foldProfile_base M hM

theorem profile_vertical_deriv (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    deriv (fun X : ℂ => profile M hM (0, X)) 0 =
      (-(FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)) • M.complexPerronFunction hM :=
  FiniteIrreducibleNormalizedFoldActivity.foldProfile_vertical_deriv M hM

theorem profile_critical_axis (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      profile M hM (g, 0) = FiniteIrreducibleRadiusResponse.profile M hM g :=
  FiniteIrreducibleNormalizedFoldActivity.foldProfile_critical_axis M hM

/-! ## Analytic operator and rank-one spectral data -/

private abbrev PathEnd (S : Type*) [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S] :=
  C(S, ℂ) →L[ℂ] C(S, ℂ)

/- The function-space APIs carry several extensionally equal but not
definitionally equal normed structures.  We choose throughout the structures
induced by the normed ring/algebra on the endomorphism space. -/
local instance pathEndNormedRing : NormedRing (PathEnd S) := inferInstance
local instance pathEndSeminormedRing : SeminormedRing (PathEnd S) :=
  NormedRing.toSeminormedRing
@[reducible] local instance pathEndNormedAddCommGroup :
    NormedAddCommGroup (PathEnd S) :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance pathEndNormedAlgebra : NormedAlgebra ℂ (PathEnd S) := inferInstance
@[reducible] local instance pathEndNormedSpace : NormedSpace ℂ (PathEnd S) :=
  NormedAlgebra.toNormedSpace (PathEnd S)
local instance pathEndNormTopology : TopologicalSpace (PathEnd S) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance pathFunctionalNormTopology :
    TopologicalSpace (C(S, ℂ) →L[ℂ] ℂ) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Unweighted complex integration on the compact type space. -/
def scalarIntegralCLM (M : FiniteIrreducibleModel S) : C(S, ℂ) →L[ℂ] ℂ :=
  (MeasureTheory.L1.integralCLM' (α := S) (E := ℂ) (μ := M.bjrModel.mu) ℂ).comp
    (ContinuousMap.toLp 1 M.bjrModel.mu ℂ)

@[simp] theorem scalarIntegralCLM_apply (M : FiniteIrreducibleModel S)
    (f : C(S, ℂ)) :
    scalarIntegralCLM M f = ∫ x, f x ∂M.bjrModel.mu := by
  unfold scalarIntegralCLM
  rw [ContinuousLinearMap.comp_apply, ← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  exact ContinuousMap.coeFn_toLp (p := 1) (μ := M.bjrModel.mu) (𝕜 := ℂ) f

/-- The profile-to-multiplication-operator map as one continuous linear map. -/
def profileMultiplierCLM :=
  letI : SeminormedAddCommGroup C(S, ℂ) :=
    NormedAddCommGroup.toSeminormedAddCommGroup
  letI : Module ℂ C(S, ℂ) := NormedSpace.toModule
  letI : TopologicalSpace C(S, ℂ) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  (ContinuousLinearMap.apply ℂ (PathEnd S) (1 : C(S, ℂ))).comp
    (ContinuousLinearMap.mulLeftRight ℂ C(S, ℂ))

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem profileMultiplierCLM_apply (tau : C(S, ℂ)) :
    profileMultiplierCLM tau = GraphCore.pathProfileMultiplier tau := by
  rfl

/-- The analytic operator family `tau ↦ K M_tau`. -/
def pathOperatorParameterCLM (M : FiniteIrreducibleModel S) :=
  ((ContinuousLinearMap.compL ℂ C(S, ℂ) C(S, ℂ) C(S, ℂ))
      (M.bjrModel.kernel.complexActionCLM M.bjrModel.mu)).comp profileMultiplierCLM

/-- The paper's path operator `L(g,X) = K M_{T(g,X)}`. -/
def pathOperator (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : PathEnd S :=
  pathOperatorParameterCLM M (profile M hM q)

@[simp] theorem pathOperator_apply (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) (f : C(S, ℂ)) :
    pathOperator M hM q f =
      M.bjrModel.kernel.complexAction M.bjrModel.mu (profile M hM q * f) := by
  simp only [pathOperator, pathOperatorParameterCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    profileMultiplierCLM_apply,
    GraphCore.pathProfileMultiplier_apply,
    ContinuousKernel.complexActionCLM_apply]

theorem pathOperator_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (pathOperator M hM) (0, 0) := by
  change AnalyticAt ℂ
    (fun q => pathOperatorParameterCLM M (profile M hM q)) (0, 0)
  simpa only [Function.comp_def] using
    ((pathOperatorParameterCLM M).analyticAt
      (profile M hM (0, 0))).comp (profile_analytic M hM)

theorem pathOperator_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    pathOperator M hM (0, 0) = M.bjrModel.kernel.complexActionCLM M.bjrModel.mu := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [pathOperator_apply, profile_base, one_mul,
    ContinuousKernel.complexActionCLM_apply]

/-- The analytic Perron eigenvalue along the actual joint chart. -/
def eigenvalue (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  FiniteIrreducibleCriticalPair.eigenvalue M hM (profile M hM q)

/-- The analytic Perron eigenvector along the actual joint chart. -/
def eigenvector (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : C(S, ℂ) :=
  FiniteIrreducibleCriticalPair.eigenvector M hM (profile M hM q)

theorem eigenvalue_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (eigenvalue M hM) (0, 0) :=
  (FiniteIrreducibleCriticalPair.eigenvalue_analytic M hM).comp_of_eq
    (profile_analytic M hM) (profile_base M hM)

theorem eigenvector_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (eigenvector M hM) (0, 0) :=
  (FiniteIrreducibleCriticalPair.eigenvector_analytic M hM).comp_of_eq
    (profile_analytic M hM) (profile_base M hM)

@[simp] theorem eigenvalue_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    eigenvalue M hM (0, 0) = 1 := by
  rw [eigenvalue, profile_base, FiniteIrreducibleCriticalPair.eigenvalue_base]

@[simp] theorem eigenvector_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    eigenvector M hM (0, 0) = M.complexPerronFunction hM := by
  rw [eigenvector, profile_base, FiniteIrreducibleCriticalPair.eigenvector_base]

/-- The raw left eigenfunctional with weight `tau * v`. -/
def pairingFunctionalParameterCLM (M : FiniteIrreducibleModel S) :=
  ((ContinuousLinearMap.compL ℂ C(S, ℂ) C(S, ℂ) ℂ)
      (scalarIntegralCLM M)).comp profileMultiplierCLM

def pairingFunctional (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : C(S, ℂ) →L[ℂ] ℂ :=
  pairingFunctionalParameterCLM M
    (profile M hM q * eigenvector M hM q)

@[simp] theorem pairingFunctional_apply (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) (f : C(S, ℂ)) :
      pairingFunctional M hM q f =
      ∫ x, profile M hM q x * eigenvector M hM q x * f x ∂M.bjrModel.mu := by
  simp only [pairingFunctional, pairingFunctionalParameterCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    profileMultiplierCLM_apply, GraphCore.pathProfileMultiplier_apply,
    scalarIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousMap.mul_apply]

theorem pairingFunctional_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (pairingFunctional M hM) (0, 0) := by
  have hprod : AnalyticAt ℂ
      (fun q => profile M hM q * eigenvector M hM q) (0, 0) :=
    (profile_analytic M hM).mul (eigenvector_analytic M hM)
  change AnalyticAt ℂ
    (fun q => pairingFunctionalParameterCLM M
      (profile M hM q * eigenvector M hM q)) (0, 0)
  simpa only [Function.comp_def] using
    ((pairingFunctionalParameterCLM M).analyticAt
      (profile M hM (0, 0) * eigenvector M hM (0, 0))).comp_of_eq hprod rfl

/-- The normalization `q(g,X)=∫ T(g,X) v(g,X)^2`. -/
def pairingNormalizer (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  scalarIntegralCLM M
    (profile M hM q * eigenvector M hM q * eigenvector M hM q)

theorem pairingNormalizer_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (pairingNormalizer M hM) (0, 0) := by
  exact (scalarIntegralCLM M).analyticAt _ |>.comp
    (((profile_analytic M hM).mul (eigenvector_analytic M hM)).mul
      (eigenvector_analytic M hM))

@[simp] theorem pairingNormalizer_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    pairingNormalizer M hM (0, 0) = (M.alpha hM : ℂ) := by
  simp only [pairingNormalizer, profile_base, eigenvector_base,
    one_mul, scalarIntegralCLM_apply]
  change (∫ x, (M.complexPerronFunction hM * M.complexPerronFunction hM) x
    ∂M.measure) = (M.alpha hM : ℂ)
  rw [M.integral_measure]
  simp only [ContinuousMap.mul_apply, FiniteIrreducibleModel.complexPerronFunction_apply,
    Complex.real_smul, FiniteIrreducibleModel.alpha, FiniteIrreducibleModel.average,
    Complex.ofReal_sum, Complex.ofReal_mul, pow_two]

theorem pairingNormalizer_base_ne_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    pairingNormalizer M hM (0, 0) ≠ 0 := by
  rw [pairingNormalizer_base]
  exact Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne'

/-- The normalized analytic rank-one Perron projection. -/
def spectralProjection (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : PathEnd S :=
  (pairingNormalizer M hM q)⁻¹ •
    (pairingFunctional M hM q).smulRight (eigenvector M hM q)

theorem spectralProjection_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (spectralProjection M hM) (0, 0) := by
  have hn := pairingNormalizer_base_ne_zero M hM
  have hinv : AnalyticAt ℂ (fun q => (pairingNormalizer M hM q)⁻¹) (0, 0) :=
    (pairingNormalizer_analytic M hM).inv hn
  have hrank : AnalyticAt ℂ
      (fun q => (pairingFunctional M hM q).smulRight (eigenvector M hM q))
      (0, 0) := by
    exact ((ContinuousLinearMap.smulRightL ℂ C(S, ℂ) C(S, ℂ)).analyticAt_bilinear
      (pairingFunctional M hM (0, 0), eigenvector M hM (0, 0))).comp₂
        (pairingFunctional_analytic M hM) (eigenvector_analytic M hM)
  exact hinv.smul hrank

@[simp] theorem spectralProjection_apply (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) (f : C(S, ℂ)) :
    spectralProjection M hM q f =
      ((pairingNormalizer M hM q)⁻¹ * pairingFunctional M hM q f) •
        eigenvector M hM q := by
  simp [spectralProjection, smul_smul]

/-- The actual atomic-law left functional is the true integral pairing. -/
theorem weightedFunctional_eq_integral (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (f : C(S, ℂ)) :
    M.weightedFunctional hM f =
      ∫ x, (M.perronFunction hM x : ℂ) * f x ∂M.bjrModel.mu := by
  rw [M.weightedFunctional_apply, FiniteIrreducibleModel.bjrModel_mu, M.integral_measure]
  simp only [Complex.real_smul, Complex.ofReal_mul, mul_assoc]

theorem spectralProjection_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    spectralProjection M hM (0, 0) = M.perronProjection hM := by
  apply ContinuousLinearMap.ext
  intro f
  rw [spectralProjection_apply, M.perronProjection_apply,
    pairingNormalizer_base, eigenvector_base]
  change ((M.alpha hM : ℂ)⁻¹ * pairingFunctional M hM (0, 0) f) •
      M.complexPerronFunction hM =
    ((M.alpha hM : ℂ)⁻¹ * M.weightedFunctional hM f) •
      M.complexPerronFunction hM
  congr 1
  rw [pairingFunctional_apply, profile_base, eigenvector_base,
    weightedFunctional_eq_integral]
  simp only [ContinuousMap.one_apply, one_mul,
    FiniteIrreducibleModel.complexPerronFunction_apply]

theorem eigenpair_equations (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      pathOperator M hM q (eigenvector M hM q) =
          eigenvalue M hM q • eigenvector M hM q ∧
        M.normalizedPerronFunctional hM (eigenvector M hM q) = 1 := by
  have ht : Filter.Tendsto (profile M hM) (𝓝 (0, 0)) (𝓝 1) := by
    simpa only [profile_base] using (profile_analytic M hM).continuousAt.tendsto
  filter_upwards [ht.eventually (FiniteIrreducibleCriticalPair.eigenpair_equations M hM)] with q hq
  constructor
  · rw [pathOperator_apply]
    change M.complexOperator
      (profile M hM q * FiniteIrreducibleCriticalPair.eigenvector M hM (profile M hM q)) = _
    exact hq.1
  · exact hq.2

theorem eigenvalue_critical_axis (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0, eigenvalue M hM (g, 0) = 1 := by
  have hcrit := (Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hM)).2.2.1
  filter_upwards [profile_critical_axis M hM, hcrit] with g hprofile hg
  rw [eigenvalue, hprofile]
  exact hg.2

theorem pairingNormalizer_ne_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), pairingNormalizer M hM q ≠ 0 :=
  (pairingNormalizer_analytic M hM).continuousAt.eventually_ne
    (pairingNormalizer_base_ne_zero M hM)

/-- Kernel symmetry converts the right eigenvector into the genuine left
eigenfunctional for `K M_T`; no adjoint or extra spectral assumption enters. -/
theorem pairingFunctional_pathOperator (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), ∀ f : C(S, ℂ),
      pairingFunctional M hM q (pathOperator M hM q f) =
        eigenvalue M hM q * pairingFunctional M hM q f := by
  filter_upwards [eigenpair_equations M hM] with q hq f
  let tau := profile M hM q
  let v := eigenvector M hM q
  let lam := eigenvalue M hM q
  calc
    pairingFunctional M hM q (pathOperator M hM q f) =
        ∫ x, (tau * v) x *
          M.bjrModel.kernel.complexAction M.bjrModel.mu (tau * f) x ∂M.bjrModel.mu := by
      rw [pairingFunctional_apply, pathOperator_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [ContinuousMap.mul_apply, tau, v]
    _ = ∫ x, (tau * f) x *
          M.bjrModel.kernel.complexAction M.bjrModel.mu (tau * v) x ∂M.bjrModel.mu :=
      TreeFoldUniformField.complexAction_pairing_symm M.bjrModel (tau * v) (tau * f)
    _ = lam * pairingFunctional M hM q f := by
      rw [show M.bjrModel.kernel.complexAction M.bjrModel.mu (tau * v) = lam • v by
        simpa only [pathOperator_apply, tau, v, lam] using hq.1]
      rw [pairingFunctional_apply, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul,
        tau, v, lam]
      ring

theorem spectralProjection_eigenvector (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      spectralProjection M hM q (eigenvector M hM q) =
        eigenvector M hM q := by
  filter_upwards [pairingNormalizer_ne_zero M hM] with q hn
  rw [spectralProjection_apply]
  have hpair : pairingFunctional M hM q (eigenvector M hM q) =
      pairingNormalizer M hM q := by
    rw [pairingFunctional_apply]
    unfold pairingNormalizer
    rw [scalarIntegralCLM_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [ContinuousMap.mul_apply]
  rw [hpair, inv_mul_cancel₀ hn, one_smul]

theorem spectralProjection_idempotent (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      spectralProjection M hM q * spectralProjection M hM q =
        spectralProjection M hM q := by
  filter_upwards [spectralProjection_eigenvector M hM] with q hv
  apply ContinuousLinearMap.ext
  intro f
  change spectralProjection M hM q (spectralProjection M hM q f) = _
  let c := (pairingNormalizer M hM q)⁻¹ * pairingFunctional M hM q f
  have hform : spectralProjection M hM q f = c • eigenvector M hM q := by
    rw [spectralProjection_apply]
  calc
    spectralProjection M hM q (spectralProjection M hM q f) =
        spectralProjection M hM q (c • eigenvector M hM q) := by rw [hform]
    _ = c • spectralProjection M hM q (eigenvector M hM q) := map_smul _ _ _
    _ = c • eigenvector M hM q := by rw [hv]
    _ = spectralProjection M hM q f := hform.symm

theorem pathOperator_mul_spectralProjection (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      pathOperator M hM q * spectralProjection M hM q =
        eigenvalue M hM q • spectralProjection M hM q := by
  filter_upwards [eigenpair_equations M hM] with q heig
  apply ContinuousLinearMap.ext
  intro f
  change pathOperator M hM q (spectralProjection M hM q f) = _
  rw [spectralProjection_apply, map_smul, heig.1]
  simp only [smul_apply, spectralProjection_apply, smul_smul]
  congr 1
  ring

theorem spectralProjection_mul_pathOperator (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      spectralProjection M hM q * pathOperator M hM q =
        eigenvalue M hM q • spectralProjection M hM q := by
  filter_upwards [pairingFunctional_pathOperator M hM] with q hleft
  apply ContinuousLinearMap.ext
  intro f
  change spectralProjection M hM q (pathOperator M hM q f) = _
  simp only [spectralProjection_apply, hleft, smul_apply, smul_smul]
  congr 1
  ring

/-- The continuous kernel of `P(g,X) K`; this is the numerator of the pole. -/
def projectedKernel (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : C(S × S, ℂ) :=
  ⟨fun p => (eigenvalue M hM q / pairingNormalizer M hM q) *
      eigenvector M hM q p.1 * eigenvector M hM q p.2, by fun_prop⟩

@[simp] theorem projectedKernel_apply (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) (a b : S) :
    projectedKernel M hM q (a, b) =
      (eigenvalue M hM q / pairingNormalizer M hM q) *
        eigenvector M hM q a * eigenvector M hM q b :=
  rfl

theorem spectralProjection_kernel_action (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), ∀ f : C(S, ℂ), ∀ a : S,
      spectralProjection M hM q (M.bjrModel.kernel.complexAction M.bjrModel.mu f) a =
        ∫ b, projectedKernel M hM q (a, b) * f b ∂M.bjrModel.mu := by
  filter_upwards [eigenpair_equations M hM,
    pairingNormalizer_ne_zero M hM] with q heig hn f a
  let tau := profile M hM q
  let v := eigenvector M hM q
  let lam := eigenvalue M hM q
  rw [spectralProjection_apply]
  have hpair : pairingFunctional M hM q (M.bjrModel.kernel.complexAction M.bjrModel.mu f) =
      lam * ∫ b, v b * f b ∂M.bjrModel.mu := by
    calc
      pairingFunctional M hM q (M.bjrModel.kernel.complexAction M.bjrModel.mu f) =
          ∫ x, (tau * v) x * M.bjrModel.kernel.complexAction M.bjrModel.mu f x ∂M.bjrModel.mu := by
        rw [pairingFunctional_apply]
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [ContinuousMap.mul_apply, tau, v]
      _ = ∫ x, f x * M.bjrModel.kernel.complexAction M.bjrModel.mu (tau * v) x ∂M.bjrModel.mu :=
        TreeFoldUniformField.complexAction_pairing_symm M.bjrModel (tau * v) f
      _ = lam * ∫ b, v b * f b ∂M.bjrModel.mu := by
        rw [show M.bjrModel.kernel.complexAction M.bjrModel.mu (tau * v) = lam • v by
          simpa only [pathOperator_apply, tau, v, lam] using heig.1]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
  rw [hpair]
  change ((pairingNormalizer M hM q)⁻¹ *
      (lam * ∫ b, v b * f b ∂M.bjrModel.mu)) * v a = _
  calc
    ((pairingNormalizer M hM q)⁻¹ *
        (lam * ∫ b, v b * f b ∂M.bjrModel.mu)) * v a =
        ((pairingNormalizer M hM q)⁻¹ * lam * v a) *
          ∫ b, v b * f b ∂M.bjrModel.mu := by ring
    _ = ∫ b, ((pairingNormalizer M hM q)⁻¹ * lam * v a) *
          (v b * f b) ∂M.bjrModel.mu := by rw [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with b
      simp only [projectedKernel_apply, v, lam, div_eq_mul_inv]
      ring

/-! ## The simple eigenvalue zero in the square-root coordinate -/

def eigenvalueGap (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  1 - eigenvalue M hM q

theorem eigenvalueGap_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (eigenvalueGap M hM) (0, 0) :=
  analyticAt_const.sub (eigenvalue_analytic M hM)

theorem eigenvalueGap_critical_axis (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0, eigenvalueGap M hM (g, 0) = 0 := by
  filter_upwards [eigenvalue_critical_axis M hM] with g hg
  simp only [eigenvalueGap, hg, sub_self]

theorem eigenvalue_vertical_deriv (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    deriv (fun X : ℂ => eigenvalue M hM (0, X)) 0 =
      -(FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) *
        ((M.beta hM : ℂ) / (M.alpha hM : ℂ)) := by
  let gamma : ℂ := FiniteIrreducibleFoldCoefficients.gamma M hM
  let u := M.complexPerronFunction hM
  have hprofileSlice : AnalyticAt ℂ (fun X : ℂ => profile M hM (0, X)) 0 :=
    (profile_analytic M hM).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl
  have hprofileDeriv : HasDerivAt (fun X : ℂ => profile M hM (0, X))
      ((-gamma) • u) 0 := by
    have h := hprofileSlice.hasStrictDerivAt.hasDerivAt
    rw [profile_vertical_deriv M hM] at h
    exact h
  have hlam : HasFDerivAt (FiniteIrreducibleCriticalPair.eigenvalue M hM)
      (fderiv ℂ (FiniteIrreducibleCriticalPair.eigenvalue M hM) 1) 1 :=
    (FiniteIrreducibleCriticalPair.eigenvalue_analytic M hM).hasStrictFDerivAt.hasFDerivAt
  have hbase : profile M hM (0, 0) = 1 := profile_base M hM
  have hcomp := hlam.comp_hasDerivAt_of_eq 0 hprofileDeriv hbase.symm
  have hderiv : deriv (fun X : ℂ => eigenvalue M hM (0, X)) 0 =
      (fderiv ℂ (FiniteIrreducibleCriticalPair.eigenvalue M hM) 1) ((-gamma) • u) := by
    simpa only [eigenvalue, hbase, Function.comp_def] using hcomp.deriv
  rw [hderiv, map_smul, smul_eq_mul,
    FiniteIrreducibleCriticalPair.eigenvalue_fderiv_perron]

theorem eigenvalueGap_vertical_deriv (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    deriv (fun X : ℂ => eigenvalueGap M hM (0, X)) 0 =
      (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) *
        ((M.beta hM : ℂ) / (M.alpha hM : ℂ)) := by
  rw [show (fun X : ℂ => eigenvalueGap M hM (0, X)) =
      (fun X : ℂ => 1 - eigenvalue M hM (0, X)) from rfl,
    deriv_const_sub, eigenvalue_vertical_deriv]
  ring

theorem eigenvalueGap_vertical_factor (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∃ Q : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) *
        ((M.beta hM : ℂ) / (M.alpha hM : ℂ)) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        eigenvalueGap M hM q = q.2 * Q q := by
  obtain ⟨Q, hQa, hfactor⟩ :=
    TreeFoldJointDivision.analytic_vertical_division
      (eigenvalueGap_analytic M hM) (eigenvalueGap_critical_axis M hM)
  refine ⟨Q, hQa, ?_, hfactor⟩
  have hsection : Filter.Tendsto
      (fun X : ℂ => ((0 : C(S, ℂ)), X)) (𝓝 0) (𝓝 (0, 0)) :=
    (analyticAt_const.prod analyticAt_id : AnalyticAt ℂ
      (fun X : ℂ => ((0 : C(S, ℂ)), X)) 0).continuousAt.tendsto
  have hslice : (fun X : ℂ => eigenvalueGap M hM (0, X)) =ᶠ[𝓝 0]
      (fun X => X * Q (0, X)) := by
    filter_upwards [hsection.eventually hfactor] with X hX
    exact hX
  have hQslice : AnalyticAt ℂ (fun X : ℂ => Q (0, X)) 0 :=
    hQa.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hprod : HasDerivAt (fun X : ℂ => X * Q (0, X)) (Q (0, 0)) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).mul hQslice.differentiableAt.hasDerivAt
    have hfun : id * (fun X : ℂ => Q (0, X)) =
        (fun X => X * Q (0, X)) := by
      rfl
    rw [hfun] at h
    simpa only [id, one_mul, zero_mul, add_zero] using h
  have heq := hslice.deriv_eq
  rw [hprod.deriv, eigenvalueGap_vertical_deriv M hM] at heq
  exact heq.symm

/-- Canonical analytic quotient in `1 - lambda(g,X) = X Q(g,X)`. -/
def gapQuotient (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    C(S, ℂ) × ℂ → ℂ :=
  Classical.choose (eigenvalueGap_vertical_factor M hM)

theorem gapQuotient_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (gapQuotient M hM) (0, 0) :=
  (Classical.choose_spec (eigenvalueGap_vertical_factor M hM)).1

@[simp] theorem gapQuotient_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    gapQuotient M hM (0, 0) =
      (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) *
        ((M.beta hM : ℂ) / (M.alpha hM : ℂ)) :=
  (Classical.choose_spec (eigenvalueGap_vertical_factor M hM)).2.1

theorem eigenvalueGap_eq_mul_gapQuotient (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      eigenvalueGap M hM q = q.2 * gapQuotient M hM q :=
  (Classical.choose_spec (eigenvalueGap_vertical_factor M hM)).2.2

theorem gapQuotient_base_ne_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) : gapQuotient M hM (0, 0) ≠ 0 := by
  rw [gapQuotient_base]
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (FiniteIrreducibleFoldCoefficients.gamma_pos M hM).ne')
    (div_ne_zero (Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne')
      (Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne'))

theorem gapQuotient_ne_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), gapQuotient M hM q ≠ 0 :=
  (gapQuotient_analytic M hM).continuousAt.eventually_ne
    (gapQuotient_base_ne_zero M hM)

/-- The analytic kernel multiplying the explicit pole `X⁻¹`. -/
def poleKernel (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : C(S × S, ℂ) :=
  (gapQuotient M hM q)⁻¹ • projectedKernel M hM q

@[simp] theorem poleKernel_apply (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) (a b : S) :
    poleKernel M hM q (a, b) =
      ((eigenvalue M hM q /
          (pairingNormalizer M hM q * gapQuotient M hM q)) *
        eigenvector M hM q a * eigenvector M hM q b) := by
  simp only [poleKernel, ContinuousMap.smul_apply, smul_eq_mul,
    projectedKernel_apply, div_eq_mul_inv]
  ring

/-- The residue kernel depends only on the field and is obtained by setting
the square-root coordinate to zero in the analytic pole numerator. -/
def residueKernel (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℂ)) : C(S × S, ℂ) :=
  poleKernel M hM (g, 0)

theorem projectedKernel_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (projectedKernel M hM) (0, 0) := by
  let fstMap : C(S × S, S) := ⟨Prod.fst, continuous_fst⟩
  let sndMap : C(S × S, S) := ⟨Prod.snd, continuous_snd⟩
  have hv1 : AnalyticAt ℂ
      (fun q => (ContinuousMap.compCLM ℂ ℂ fstMap) (eigenvector M hM q))
      (0, 0) :=
    (ContinuousMap.compCLM ℂ ℂ fstMap).analyticAt _ |>.comp
      (eigenvector_analytic M hM)
  have hv2 : AnalyticAt ℂ
      (fun q => (ContinuousMap.compCLM ℂ ℂ sndMap) (eigenvector M hM q))
      (0, 0) :=
    (ContinuousMap.compCLM ℂ ℂ sndMap).analyticAt _ |>.comp
      (eigenvector_analytic M hM)
  have hscalar : AnalyticAt ℂ
      (fun q => eigenvalue M hM q / pairingNormalizer M hM q) (0, 0) :=
    (eigenvalue_analytic M hM).div (pairingNormalizer_analytic M hM)
      (pairingNormalizer_base_ne_zero M hM)
  have hformula : projectedKernel M hM =
      fun q => (eigenvalue M hM q / pairingNormalizer M hM q) •
        ((ContinuousMap.compCLM ℂ ℂ fstMap) (eigenvector M hM q) *
          (ContinuousMap.compCLM ℂ ℂ sndMap) (eigenvector M hM q)) := by
    funext q
    ext p
    change (eigenvalue M hM q / pairingNormalizer M hM q) *
        eigenvector M hM q p.1 * eigenvector M hM q p.2 =
      (eigenvalue M hM q / pairingNormalizer M hM q) *
        (eigenvector M hM q p.1 * eigenvector M hM q p.2)
    ring
  rw [hformula]
  exact hscalar.smul (hv1.mul hv2)

theorem poleKernel_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (poleKernel M hM) (0, 0) :=
  ((gapQuotient_analytic M hM).inv (gapQuotient_base_ne_zero M hM)).smul
    (projectedKernel_analytic M hM)

theorem residueKernel_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (residueKernel M hM) 0 :=
  (poleKernel_analytic M hM).comp_of_eq
    (analyticAt_id.prod analyticAt_const) rfl

/-- Analytic variation of the pole numerator in the square-root coordinate. -/
private theorem poleKernel_vertical_difference_factor
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ R : C(S, ℂ) × ℂ → C(S × S, ℂ),
      AnalyticAt ℂ R (0, 0) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        poleKernel M hM q = residueKernel M hM q.1 + q.2 • R q := by
  obtain ⟨R, hRa, hfactor⟩ :=
    AnalyticVerticalDivision.analytic_vertical_difference_division
      (poleKernel_analytic M hM)
  refine ⟨R, hRa, ?_⟩
  filter_upwards [hfactor] with q hq
  have hbase : poleKernel M hM (q.1, 0) = residueKernel M hM q.1 := rfl
  rw [hbase] at hq
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hq)

private def poleRemainder (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) : C(S, ℂ) × ℂ → C(S × S, ℂ) :=
  Classical.choose (poleKernel_vertical_difference_factor M hM)

private theorem poleRemainder_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (poleRemainder M hM) (0, 0) :=
  (Classical.choose_spec (poleKernel_vertical_difference_factor M hM)).1

private theorem poleKernel_eq_residue_add (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      poleKernel M hM q =
        residueKernel M hM q.1 + q.2 • poleRemainder M hM q :=
  (Classical.choose_spec (poleKernel_vertical_difference_factor M hM)).2

theorem residueKernel_base_coefficient (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (a b : S) :
    residueKernel M hM 0 (a, b) =
      (1 / ((FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) * (M.beta hM : ℂ))) *
        M.complexPerronFunction hM a * M.complexPerronFunction hM b := by
  simp only [residueKernel, poleKernel_apply, eigenvalue_base,
    pairingNormalizer_base, gapQuotient_base, eigenvector_base]
  have ha : (M.alpha hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne'
  have hb : (M.beta hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne'
  have hg : (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FiniteIrreducibleFoldCoefficients.gamma_pos M hM).ne'
  field_simp

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem gamma_mul_beta_eq_sqrt_two_beta (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    FiniteIrreducibleFoldCoefficients.gamma M hM * M.beta hM =
      Real.sqrt (2 * M.beta hM) := by
  have hleft : 0 < FiniteIrreducibleFoldCoefficients.gamma M hM * M.beta hM :=
    mul_pos (FiniteIrreducibleFoldCoefficients.gamma_pos M hM) (M.beta_pos hM)
  have hright : 0 < Real.sqrt (2 * M.beta hM) := by
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) (M.beta_pos hM))
  have hsquareLeft :
      (FiniteIrreducibleFoldCoefficients.gamma M hM * M.beta hM) ^ 2 =
        2 * M.beta hM := by
    calc
      _ = (FiniteIrreducibleFoldCoefficients.gamma M hM ^ 2 * M.beta hM) * M.beta hM := by ring
      _ = 2 * M.beta hM := by rw [FiniteIrreducibleFoldCoefficients.gamma_sq_mul_beta]
  have hsquareRight : (Real.sqrt (2 * M.beta hM)) ^ 2 =
      2 * M.beta hM := by
    exact Real.sq_sqrt (mul_nonneg (by norm_num) (M.beta_pos hM).le)
  nlinarith

theorem residueKernel_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (a b : S) :
    residueKernel M hM 0 (a, b) =
      M.complexPerronFunction hM a * M.complexPerronFunction hM b /
        (Real.sqrt (2 * M.beta hM) : ℂ) := by
  rw [residueKernel_base_coefficient]
  have hscale :
      ((FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) * (M.beta hM : ℂ)) =
        (Real.sqrt (2 * M.beta hM) : ℂ) := by
    exact_mod_cast gamma_mul_beta_eq_sqrt_two_beta M hM
  rw [hscale]
  ring

/-! ## Analytic complementary inverse -/

/-- The spectral complement `C=L-lambda P`. -/
def complementOperator (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : PathEnd S :=
  pathOperator M hM q - eigenvalue M hM q • spectralProjection M hM q

theorem complementOperator_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (complementOperator M hM) (0, 0) :=
  (pathOperator_analytic M hM).sub
    ((eigenvalue_analytic M hM).smul (spectralProjection_analytic M hM))

@[simp] theorem complementOperator_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    complementOperator M hM (0, 0) =
      M.bjrModel.kernel.complexActionCLM M.bjrModel.mu - M.perronProjection hM := by
  simp only [complementOperator, pathOperator_base, eigenvalue_base,
    one_smul, spectralProjection_base]

def complementDenominator (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : PathEnd S :=
  1 - complementOperator M hM q

theorem complementDenominator_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (complementDenominator M hM) (0, 0) :=
  analyticAt_const.sub (complementOperator_analytic M hM)

@[simp] theorem complementDenominator_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    complementDenominator M hM (0, 0) =
      1 - M.bjrModel.kernel.complexActionCLM M.bjrModel.mu + M.perronProjection hM := by
  rw [complementDenominator, complementOperator_base]
  abel

theorem complementDenominator_base_isUnit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    IsUnit (complementDenominator M hM (0, 0)) := by
  rw [complementDenominator_base]
  exact M.augmented_kernel_isUnit hM

theorem complementDenominator_isUnit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      IsUnit (complementDenominator M hM q) := by
  have hopen : {y : PathEnd S | IsUnit y} ∈
      𝓝 (complementDenominator M hM (0, 0)) :=
    IsOpen.mem_nhds Units.isOpen (complementDenominator_base_isUnit M hM)
  exact (complementDenominator_analytic M hM).continuousAt.tendsto.eventually hopen

/-- The analytic inverse of `I-C` on the complementary spectral block. -/
def complementResolvent (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : PathEnd S :=
  Ring.inverse (complementDenominator M hM q)

theorem complementResolvent_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (complementResolvent M hM) (0, 0) := by
  let hzUnit := complementDenominator_base_isUnit M hM
  let z := hzUnit.unit
  have hz : (z : PathEnd S) = complementDenominator M hM (0, 0) :=
    hzUnit.unit_spec
  have hcomp := (analyticAt_inverse (𝕜 := ℂ) z).comp_of_eq
    (complementDenominator_analytic M hM) hz.symm
  change @AnalyticAt ℂ (C(S, ℂ) × ℂ) (PathEnd S)
    _ _ _
    NonUnitalNormedRing.toNormedAddCommGroup
    (NormedAlgebra.toNormedSpace (PathEnd S))
    (fun q => Ring.inverse (complementDenominator M hM q)) (0, 0)
  exact hcomp

theorem complementOperator_mul_projection (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      complementOperator M hM q * spectralProjection M hM q = 0 := by
  filter_upwards [pathOperator_mul_spectralProjection M hM,
    spectralProjection_idempotent M hM] with q hLP hPP
  rw [complementOperator, sub_mul, hLP, smul_mul_assoc, hPP, sub_self]

theorem projection_mul_complementOperator (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      spectralProjection M hM q * complementOperator M hM q = 0 := by
  filter_upwards [spectralProjection_mul_pathOperator M hM,
    spectralProjection_idempotent M hM] with q hPL hPP
  rw [complementOperator, mul_sub, hPL, mul_smul_comm, hPP, sub_self]

/-- The operator-valued analytic coefficient of the explicit `X⁻¹` pole. -/
def poleOperator (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : PathEnd S :=
  (gapQuotient M hM q)⁻¹ •
    (spectralProjection M hM q * M.bjrModel.kernel.complexActionCLM M.bjrModel.mu)

theorem poleOperator_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (poleOperator M hM) (0, 0) := by
  have hK : AnalyticAt ℂ
      (fun _ : C(S, ℂ) × ℂ => M.bjrModel.kernel.complexActionCLM M.bjrModel.mu) (0, 0) :=
    analyticAt_const
  have hprod : AnalyticAt ℂ
      (fun q => spectralProjection M hM q * M.bjrModel.kernel.complexActionCLM M.bjrModel.mu)
      (0, 0) :=
    (spectralProjection_analytic M hM).mul hK
  exact ((gapQuotient_analytic M hM).inv
    (gapQuotient_base_ne_zero M hM)).smul hprod

/-- The analytic complementary part of `(I-L)⁻¹K`. -/
def regularOperator (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : PathEnd S :=
  complementResolvent M hM q *
    (1 - spectralProjection M hM q) * M.bjrModel.kernel.complexActionCLM M.bjrModel.mu

theorem regularOperator_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (regularOperator M hM) (0, 0) := by
  have hOneMinus : AnalyticAt ℂ
      (fun q => (1 : PathEnd S) - spectralProjection M hM q) (0, 0) :=
    analyticAt_const.sub (spectralProjection_analytic M hM)
  have hK : AnalyticAt ℂ
      (fun _ : C(S, ℂ) × ℂ => M.bjrModel.kernel.complexActionCLM M.bjrModel.mu) (0, 0) :=
    analyticAt_const
  exact ((complementResolvent_analytic M hM).mul hOneMinus).mul hK

/-- The literal path resolvent in the operator algebra.  Away from the fold
it is the inverse of `I-L`, followed by the endpoint kernel `K`. -/
def pathResolvent (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : PathEnd S :=
  Ring.inverse (1 - pathOperator M hM q) * M.bjrModel.kernel.complexActionCLM M.bjrModel.mu

theorem inverse_rank_one_split (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      Ring.inverse (1 - pathOperator M hM q) =
        q.2⁻¹ • ((gapQuotient M hM q)⁻¹ • spectralProjection M hM q) +
          complementResolvent M hM q * (1 - spectralProjection M hM q) := by
  filter_upwards [spectralProjection_idempotent M hM,
    complementOperator_mul_projection M hM,
    projection_mul_complementOperator M hM,
    complementDenominator_isUnit M hM,
    eigenvalueGap_eq_mul_gapQuotient M hM,
    gapQuotient_ne_zero M hM] with q hPP hCP hPC hDunit hfactor hQne hX
  let P := spectralProjection M hM q
  let C := complementOperator M hM q
  let D := complementDenominator M hM q
  let R := complementResolvent M hM q
  let lam := eigenvalue M hM q
  let gap := eigenvalueGap M hM q
  have hgap : gap ≠ 0 := by
    change eigenvalueGap M hM q ≠ 0
    rw [hfactor]
    exact mul_ne_zero hX hQne
  have hDdef : D = 1 - C := rfl
  have hRdef : R = Ring.inverse D := rfl
  let unitD := hDunit.unit
  have hunitD : (unitD : PathEnd S) = D := hDunit.unit_spec
  have hDR : D * R = 1 := by
    rw [hRdef, ← hunitD, Ring.inverse_unit]
    exact unitD.mul_inv
  have hRD : R * D = 1 := by
    rw [hRdef, ← hunitD, Ring.inverse_unit]
    exact unitD.inv_mul
  have hDP : D * P = P := by
    rw [hDdef, sub_mul, one_mul, hCP, sub_zero]
  have hPD : P * D = P := by
    rw [hDdef, mul_sub, mul_one, hPC, sub_zero]
  have hRP : R * P = P := by
    calc
      R * P = R * (D * P) := by rw [hDP]
      _ = (R * D) * P := by rw [mul_assoc]
      _ = P := by rw [hRD, one_mul]
  have hPR : P * R = P := by
    calc
      P * R = (P * D) * R := by rw [hPD]
      _ = P * (D * R) := by rw [mul_assoc]
      _ = P := by rw [hDR, mul_one]
  have hL : pathOperator M hM q = C + lam • P := by
    change pathOperator M hM q =
      complementOperator M hM q +
        eigenvalue M hM q • spectralProjection M hM q
    unfold complementOperator
    abel
  let B : PathEnd S := gap⁻¹ • P + R * (1 - P)
  have hgap_def : gap = 1 - lam := rfl
  have hgapScalar : gap⁻¹ - lam * gap⁻¹ = 1 := by
    calc
      gap⁻¹ - lam * gap⁻¹ = (1 - lam) * gap⁻¹ := by ring
      _ = gap * gap⁻¹ := by rw [hgap_def]
      _ = 1 := mul_inv_cancel₀ hgap
  have hgapScalar' : gap⁻¹ - gap⁻¹ * lam = 1 := by
    simpa only [mul_comm] using hgapScalar
  have hfirstLeft : (D - lam • P) * (gap⁻¹ • P) = P := by
    calc
      (D - lam • P) * (gap⁻¹ • P) =
          gap⁻¹ • (D * P) - lam • (gap⁻¹ • (P * P)) := by
            rw [sub_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
      _ = gap⁻¹ • P - (lam * gap⁻¹) • P := by
        rw [hDP, hPP, smul_smul]
      _ = (gap⁻¹ - lam * gap⁻¹) • P :=
        (sub_smul gap⁻¹ (lam * gap⁻¹) P).symm
      _ = P := by rw [hgapScalar, one_smul]
  have hsecondLeft : (D - lam • P) * (R * (1 - P)) = 1 - P := by
    have hone : D * (R * (1 - P)) = 1 - P := by
      rw [← mul_assoc, hDR, one_mul]
    have hz : (lam • P) * (R * (1 - P)) = 0 := by
      rw [← mul_assoc, smul_mul_assoc, hPR, smul_mul_assoc]
      rw [mul_sub, mul_one, hPP, sub_self, smul_zero]
    rw [sub_mul, hone, hz, sub_zero]
  have hfirstRight : (gap⁻¹ • P) * (D - lam • P) = P := by
    calc
      (gap⁻¹ • P) * (D - lam • P) =
          gap⁻¹ • (P * D) - (gap⁻¹ * lam) • (P * P) := by
            rw [mul_sub, smul_mul_assoc, smul_mul_assoc,
              mul_smul_comm, smul_smul]
      _ = gap⁻¹ • P - (gap⁻¹ * lam) • P := by rw [hPD, hPP]
      _ = (gap⁻¹ - gap⁻¹ * lam) • P :=
        (sub_smul gap⁻¹ (gap⁻¹ * lam) P).symm
      _ = P := by rw [hgapScalar', one_smul]
  have hsecondRight : (R * (1 - P)) * (D - lam • P) = 1 - P := by
    have hone : (R * (1 - P)) * D = 1 - P := by
      calc
        (R * (1 - P)) * D = R * ((1 - P) * D) := mul_assoc _ _ _
        _ = R * (D - P) := by rw [sub_mul, one_mul, hPD]
        _ = R * D - R * P := by rw [mul_sub]
        _ = 1 - P := by rw [hRD, hRP]
    have hzero : (R * (1 - P)) * (lam • P) = 0 := by
      rw [mul_smul_comm, mul_assoc]
      rw [sub_mul, one_mul, hPP, sub_self, mul_zero, smul_zero]
    rw [mul_sub, hone, hzero, sub_zero]
  have hleft : (1 - pathOperator M hM q) * B = 1 := by
    change (1 - pathOperator M hM q) *
      (gap⁻¹ • P + R * (1 - P)) = 1
    rw [hL, show 1 - (C + lam • P) = D - lam • P by rw [hDdef]; abel]
    rw [mul_add, hfirstLeft, hsecondLeft]
    abel
  have hright : B * (1 - pathOperator M hM q) = 1 := by
    change (gap⁻¹ • P + R * (1 - P)) *
      (1 - pathOperator M hM q) = 1
    rw [hL, show 1 - (C + lam • P) = D - lam • P by rw [hDdef]; abel]
    rw [add_mul, hfirstRight, hsecondRight]
    abel
  let u : (PathEnd S)ˣ :=
    { val := 1 - pathOperator M hM q
      inv := B
      val_inv := hleft
      inv_val := hright }
  have hinverse : Ring.inverse (1 - pathOperator M hM q) = B := by
    change Ring.inverse (u : PathEnd S) = B
    rw [Ring.inverse_unit]
    rfl
  have hgapInvFactor :
      gap⁻¹ = q.2⁻¹ * (gapQuotient M hM q)⁻¹ := by
    change (eigenvalueGap M hM q)⁻¹ = _
    rw [hfactor]
    field_simp [hX, hQne]
  rw [hinverse]
  change gap⁻¹ • P + R * (1 - P) =
    q.2⁻¹ • ((gapQuotient M hM q)⁻¹ • P) + R * (1 - P)
  rw [hgapInvFactor, mul_smul]

theorem pathResolvent_rank_one_split (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      pathResolvent M hM q =
        q.2⁻¹ • poleOperator M hM q + regularOperator M hM q := by
  filter_upwards [inverse_rank_one_split M hM] with q hsplit hX
  rw [pathResolvent, hsplit hX, add_mul, smul_mul_assoc,
    poleOperator, regularOperator]
  simp only [smul_mul_assoc, smul_smul]

/-! ## Continuous kernels of the split resolvent -/

/-- Apply a bounded operator to every continuous column of `K`.  The result
is again a continuous kernel.  This elementary map is the bridge that turns
the operator-valued analytic splitting into the paper's `C(S^2)` statement.
-/
def operatorKernelizeLinearMap (M : FiniteIrreducibleModel S) :
    PathEnd S →ₗ[ℂ] C(S × S, ℂ) where
  toFun B :=
    ⟨fun p => B (M.bjrModel.kernel.complexColumns p.2) p.1, by fun_prop⟩
  map_add' B₁ B₂ := by
    ext p
    simp
  map_smul' c B := by
    ext p
    simp

def operatorKernelize (M : FiniteIrreducibleModel S) :
    PathEnd S →L[ℂ] C(S × S, ℂ) :=
  (operatorKernelizeLinearMap M).mkContinuous ‖M.bjrModel.kernel.toContinuousMap‖ (by
    intro B
    apply (ContinuousMap.norm_le _
      (mul_nonneg (norm_nonneg M.bjrModel.kernel.toContinuousMap) (norm_nonneg B))).2
    intro p
    calc
      ‖B (M.bjrModel.kernel.complexColumns p.2) p.1‖ ≤
          ‖B (M.bjrModel.kernel.complexColumns p.2)‖ :=
        (B (M.bjrModel.kernel.complexColumns p.2)).norm_coe_le_norm p.1
      _ ≤ ‖B‖ * ‖M.bjrModel.kernel.complexColumns p.2‖ := B.le_opNorm _
      _ ≤ ‖B‖ * ‖M.bjrModel.kernel.toContinuousMap‖ :=
        mul_le_mul_of_nonneg_left (M.bjrModel.kernel.norm_complexColumns_le p.2) (norm_nonneg B)
      _ = ‖M.bjrModel.kernel.toContinuousMap‖ * ‖B‖ := mul_comm _ _)

@[simp] theorem operatorKernelize_apply (M : FiniteIrreducibleModel S)
    (B : PathEnd S) (a b : S) :
    operatorKernelize M B (a, b) = B (M.bjrModel.kernel.complexColumns b) a :=
  rfl

theorem spectralProjection_kernel (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      operatorKernelize M (spectralProjection M hM q) =
        projectedKernel M hM q := by
  filter_upwards [eigenpair_equations M hM,
    pairingNormalizer_ne_zero M hM] with q heig hn
  apply ContinuousMap.ext
  rintro ⟨a, b⟩
  rw [operatorKernelize_apply, spectralProjection_apply, projectedKernel_apply]
  let tau := profile M hM q
  let v := eigenvector M hM q
  let lam := eigenvalue M hM q
  have hpair : pairingFunctional M hM q (M.bjrModel.kernel.complexColumns b) =
      lam * v b := by
    calc
      pairingFunctional M hM q (M.bjrModel.kernel.complexColumns b) =
          ∫ x, tau x * v x * (M.bjrModel.kernel x b : ℂ) ∂M.bjrModel.mu := by
        rw [pairingFunctional_apply]
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [ContinuousKernel.complexColumns_apply, tau, v]
      _ = ∫ x, (M.bjrModel.kernel b x : ℂ) * (tau * v) x ∂M.bjrModel.mu := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [show (M.bjrModel.kernel x b : ℂ) = (M.bjrModel.kernel b x : ℂ) by
          exact_mod_cast M.bjrModel.kernel.symmetric x b]
        simp only [ContinuousMap.mul_apply]
        ring
      _ = M.bjrModel.kernel.complexAction M.bjrModel.mu (tau * v) b := by
        rw [ContinuousKernel.complexAction_apply]
      _ = lam * v b := by
        have hb := congrArg (fun f : C(S, ℂ) => f b) heig.1
        simpa only [pathOperator_apply, ContinuousMap.smul_apply, smul_eq_mul,
          tau, v, lam] using hb
  rw [hpair]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The regular `C(S^2)` remainder kernel. -/
def regularKernel (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : C(S × S, ℂ) :=
  operatorKernelize M
    (complementResolvent M hM q * (1 - spectralProjection M hM q))

theorem regularKernel_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (regularKernel M hM) (0, 0) := by
  have hOneMinus : AnalyticAt ℂ
      (fun q => (1 : PathEnd S) - spectralProjection M hM q) (0, 0) :=
    analyticAt_const.sub (spectralProjection_analytic M hM)
  exact (operatorKernelize M).analyticAt _ |>.comp
    ((complementResolvent_analytic M hM).mul hOneMinus)

/-- The continuous kernel of `(I-L)⁻¹K`, defined on the punctured germ by
applying `(I-L)⁻¹` to the endpoint columns of `K`. -/
def pathResolventKernel (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : C(S × S, ℂ) :=
  operatorKernelize M (Ring.inverse (1 - pathOperator M hM q))

theorem pathResolventKernel_rank_one_split (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      pathResolventKernel M hM q =
        q.2⁻¹ • poleKernel M hM q + regularKernel M hM q := by
  filter_upwards [inverse_rank_one_split M hM,
    spectralProjection_kernel M hM] with q hsplit hkernel hX
  rw [pathResolventKernel, hsplit hX, map_add, map_smul, map_smul, hkernel]
  rfl

/-- The analytic kernel remainder after freezing the pole residue on the
critical field axis. -/
def pathRemainderKernel (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : C(S × S, ℂ) :=
  poleRemainder M hM q + regularKernel M hM q

theorem pathRemainderKernel_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (pathRemainderKernel M hM) (0, 0) :=
  (poleRemainder_analytic M hM).add (regularKernel_analytic M hM)

/-- Paper-form local pole splitting: the residue depends only on the field,
while every remaining term is jointly analytic in field and square-root
coordinate. -/
theorem pathResolventKernel_fixed_residue_split
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      pathResolventKernel M hM q =
        q.2⁻¹ • residueKernel M hM q.1 + pathRemainderKernel M hM q := by
  filter_upwards [pathResolventKernel_rank_one_split M hM,
    poleKernel_eq_residue_add M hM] with q hsplit hpole hX
  rw [hsplit hX, hpole, pathRemainderKernel, smul_add, smul_smul,
    inv_mul_cancel₀ hX, one_smul]
  abel

theorem pathResolventKernel_action (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ)
    (f : C(S, ℂ)) (a : S) :
    pathResolvent M hM q f a =
      ∫ b, pathResolventKernel M hM q (a, b) * f b ∂M.bjrModel.mu := by
  let B : PathEnd S := Ring.inverse (1 - pathOperator M hM q)
  have hint := M.bjrModel.kernel.integrable_complexActionIntegrand M.bjrModel.mu f
  have hBint := B.integral_comp_comm hint
  have hEvalInt := ContinuousMap.integral_apply (B.integrable_comp hint) a
  change (B * M.bjrModel.kernel.complexActionCLM M.bjrModel.mu) f a = _
  change B (∫ b, M.bjrModel.kernel.complexActionIntegrand f b ∂M.bjrModel.mu) a = _
  rw [← hBint, hEvalInt]
  apply integral_congr_ae
  filter_upwards [] with b
  change B (f b • M.bjrModel.kernel.complexColumns b) a =
    B (M.bjrModel.kernel.complexColumns b) a * f b
  rw [map_smul]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring


end PerronWright.FiniteIrreducibleMarkedPathResolvent
