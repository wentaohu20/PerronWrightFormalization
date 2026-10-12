import PerronWright.Analysis.FiniteIrreducibleCubicResolventAmplitude

/-!
# Integrated analytic amplitude of one labelled cubic kernel

This file upgrades the pointwise cubic-kernel amplitude to a map with values
in the Banach algebra of continuous functions on all branch coordinates.
The finite product measure integral is a continuous linear functional on
that algebra, so the integrated amplitude is jointly analytic without any
interchange of a parameter derivative with an integral.

On the punctured fold germ the integrated amplitude is exactly
`X ^ (3 * ell)` times the integral of the unrestricted marked-path
resolvent product.  At the joint base point it is the integral of the
`3 * ell`-fold frozen residue product.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Pullback of vertex and edge factors to branch-coordinate space -/

private def cubicKernelVertexCoordinateMap {ell : ℕ}
    (v : Fin (2 * ell)) : C((Fin (2 * ell) → S), S) :=
  ⟨fun x ↦ x v, continuous_apply v⟩

private def cubicKernelVertexPullbackCLM {ell : ℕ}
    (v : Fin (2 * ell)) :
    C(S, ℂ) →L[ℂ] C((Fin (2 * ell) → S), ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (cubicKernelVertexCoordinateMap v)

omit [Fintype S] [DecidableEq S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
@[simp] private theorem cubicKernelVertexPullbackCLM_apply
    {ell : ℕ} (v : Fin (2 * ell)) (tau : C(S, ℂ))
    (x : Fin (2 * ell) → S) :
    cubicKernelVertexPullbackCLM v tau x = tau (x v) :=
  rfl

private def cubicKernelEdgeCoordinateMap {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell)) :
    C((Fin (2 * ell) → S), S × S) :=
  ⟨fun x ↦
      (x (cubicKernelOrderedEndpoints K.graph e).1,
        x (cubicKernelOrderedEndpoints K.graph e).2),
    (continuous_apply (cubicKernelOrderedEndpoints K.graph e).1).prodMk
      (continuous_apply (cubicKernelOrderedEndpoints K.graph e).2)⟩

private def cubicKernelEdgePullbackCLM {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell)) :
    C(S × S, ℂ) →L[ℂ] C((Fin (2 * ell) → S), ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (cubicKernelEdgeCoordinateMap K e)

omit [Fintype S] [DecidableEq S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
@[simp] private theorem cubicKernelEdgePullbackCLM_apply
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (k : C(S × S, ℂ))
    (x : Fin (2 * ell) → S) :
    cubicKernelEdgePullbackCLM K e k x =
      k (x (cubicKernelOrderedEndpoints K.graph e).1,
        x (cubicKernelOrderedEndpoints K.graph e).2) :=
  rfl

/-! ## Continuous-function-valued finite products -/

/-- One pole-removed edge kernel, pulled back to all branch coordinates. -/
def cubicKernelNormalizedEdgeFunction
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ) :
    C((Fin (2 * ell) → S), ℂ) :=
  cubicKernelEdgePullbackCLM K e
    (boundedNormalizedPathKernel M hM q)

theorem cubicKernelNormalizedEdgeFunction_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) :
    AnalyticAt ℂ (cubicKernelNormalizedEdgeFunction M hM K e) (0, 0) := by
  unfold cubicKernelNormalizedEdgeFunction
  exact (cubicKernelEdgePullbackCLM K e).analyticAt _ |>.comp_of_eq
    (boundedNormalizedPathKernel_analytic M hM) rfl

@[simp] theorem cubicKernelNormalizedEdgeFunction_apply
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S) :
    cubicKernelNormalizedEdgeFunction M hM K e q x =
      boundedNormalizedPathKernel M hM q
        (x (cubicKernelOrderedEndpoints K.graph e).1,
          x (cubicKernelOrderedEndpoints K.graph e).2) :=
  rfl

/-- Continuous-function-valued normalized product over all cubic edges. -/
def cubicKernelNormalizedPathFunction
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) : C((Fin (2 * ell) → S), ℂ) :=
  ∏ e : Fin (3 * ell), cubicKernelNormalizedEdgeFunction M hM K e q

theorem cubicKernelNormalizedPathFunction_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    AnalyticAt ℂ (cubicKernelNormalizedPathFunction M hM K) (0, 0) := by
  unfold cubicKernelNormalizedPathFunction
  exact (Finset.univ : Finset (Fin (3 * ell))).analyticAt_fun_prod
    (fun e _ ↦ cubicKernelNormalizedEdgeFunction_analytic M hM K e)

@[simp] theorem cubicKernelNormalizedPathFunction_apply
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S) :
    cubicKernelNormalizedPathFunction M hM K q x =
      cubicKernelNormalizedPathAmplitude M hM K x q := by
  unfold cubicKernelNormalizedPathFunction
    cubicKernelNormalizedPathAmplitude
    boundedKernelNormalizedPathAmplitude
    boundedKernelNormalizedEdgeFactor
  rw [ContinuousMap.prod_apply]
  rfl

/-- The branch-profile product as one continuous function of all branch
coordinates. -/
def cubicKernelBranchProfileFunction
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (q : C(S, ℂ) × ℂ) :
    C((Fin (2 * ell) → S), ℂ) :=
  ∏ v : Fin (2 * ell),
    cubicKernelVertexPullbackCLM v (CKRA_MPR.profile M hM q)

theorem cubicKernelBranchProfileFunction_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) :
    AnalyticAt ℂ
      (cubicKernelBranchProfileFunction M hM (ell := ell)) (0, 0) := by
  unfold cubicKernelBranchProfileFunction
  apply (Finset.univ : Finset (Fin (2 * ell))).analyticAt_fun_prod
  intro v _
  exact (cubicKernelVertexPullbackCLM v).analyticAt _ |>.comp
    (CKRA_MPR.profile_analytic M hM)

@[simp] theorem cubicKernelBranchProfileFunction_apply
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S) :
    cubicKernelBranchProfileFunction M hM (ell := ell) q x =
      cubicKernelBranchProfileProduct M hM x q := by
  unfold cubicKernelBranchProfileFunction cubicKernelBranchProfileProduct
  rw [ContinuousMap.prod_apply]
  rfl

/-- The full pole-removed cubic integrand as a continuous function of all
branch coordinates. -/
def cubicKernelNormalizedIntegrandFunction
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) : C((Fin (2 * ell) → S), ℂ) :=
  cubicKernelBranchProfileFunction M hM (ell := ell) q *
    cubicKernelNormalizedPathFunction M hM K q

theorem cubicKernelNormalizedIntegrandFunction_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    AnalyticAt ℂ (cubicKernelNormalizedIntegrandFunction M hM K)
      (0, 0) :=
  (cubicKernelBranchProfileFunction_analytic M hM ell).mul
    (cubicKernelNormalizedPathFunction_analytic M hM K)

@[simp] theorem cubicKernelNormalizedIntegrandFunction_apply
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S) :
    cubicKernelNormalizedIntegrandFunction M hM K q x =
      cubicKernelNormalizedResolventIntegrand M hM K x q := by
  simp only [cubicKernelNormalizedIntegrandFunction,
    ContinuousMap.mul_apply, cubicKernelBranchProfileFunction_apply,
    cubicKernelNormalizedPathFunction_apply,
    cubicKernelNormalizedResolventIntegrand]

/-! ## The unrestricted product and the punctured identity -/

private def cubicKernelResolventEdgeFunction
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ) :
    C((Fin (2 * ell) → S), ℂ) :=
  cubicKernelEdgePullbackCLM K e
    (CKRA_MPR.pathResolventKernel M hM q)

@[simp] private theorem cubicKernelResolventEdgeFunction_apply
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S) :
    cubicKernelResolventEdgeFunction M hM K e q x =
      CKRA_MPR.pathResolventKernel M hM q
        (x (cubicKernelOrderedEndpoints K.graph e).1,
          x (cubicKernelOrderedEndpoints K.graph e).2) :=
  rfl

private def cubicKernelResolventPathFunction
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) : C((Fin (2 * ell) → S), ℂ) :=
  ∏ e : Fin (3 * ell), cubicKernelResolventEdgeFunction M hM K e q

/-- The raw pointwise resolvent integrand, packaged as one continuous
function on branch-coordinate space. -/
def cubicKernelResolventIntegrandFunction
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) : C((Fin (2 * ell) → S), ℂ) :=
  cubicKernelBranchProfileFunction M hM (ell := ell) q *
    cubicKernelResolventPathFunction M hM K q

@[simp] theorem cubicKernelResolventIntegrandFunction_apply
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S) :
    cubicKernelResolventIntegrandFunction M hM K q x =
      cubicKernelResolventIntegrand M hM K x q := by
  unfold cubicKernelResolventIntegrandFunction
    cubicKernelResolventPathFunction cubicKernelResolventEdgeFunction
    cubicKernelResolventIntegrand
  rw [ContinuousMap.mul_apply, ContinuousMap.prod_apply,
    cubicKernelBranchProfileFunction_apply]
  rfl

private theorem cubicKernelNormalizedPathFunction_eq_pow_smul
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cubicKernelNormalizedPathFunction M hM K q =
        q.2 ^ (3 * ell) • cubicKernelResolventPathFunction M hM K q := by
  filter_upwards
    [boundedNormalizedPathKernel_eq_smul_pathResolventKernel M hM] with q hq
  intro hX
  ext x
  simp only [cubicKernelNormalizedPathFunction,
    cubicKernelResolventPathFunction, ContinuousMap.prod_apply,
    cubicKernelNormalizedEdgeFunction_apply,
    cubicKernelResolventEdgeFunction_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  have hedge (e : Fin (3 * ell)) :
      boundedNormalizedPathKernel M hM q
          (x (cubicKernelOrderedEndpoints K.graph e).1,
            x (cubicKernelOrderedEndpoints K.graph e).2) =
        q.2 * CKRA_MPR.pathResolventKernel M hM q
          (x (cubicKernelOrderedEndpoints K.graph e).1,
            x (cubicKernelOrderedEndpoints K.graph e).2) := by
    have heval := congrArg
      (fun k : C(S × S, ℂ) ↦
        k (x (cubicKernelOrderedEndpoints K.graph e).1,
          x (cubicKernelOrderedEndpoints K.graph e).2))
      (hq hX)
    simpa only [ContinuousMap.smul_apply, smul_eq_mul] using heval
  simp_rw [hedge]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The continuous-function-valued normalized integrand equals the cubic
power times the raw resolvent integrand on the punctured germ. -/
theorem cubicKernelNormalizedIntegrandFunction_eq_pow_smul
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cubicKernelNormalizedIntegrandFunction M hM K q =
        q.2 ^ (3 * ell) •
          cubicKernelResolventIntegrandFunction M hM K q := by
  filter_upwards
    [cubicKernelNormalizedPathFunction_eq_pow_smul M hM K] with q hpath
  intro hX
  rw [cubicKernelNormalizedIntegrandFunction,
    cubicKernelResolventIntegrandFunction, hpath hX]
  ext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

/-! ## Continuous linear integration -/

/-- Product measure on the `2 * ell` branch coordinates. -/
def cubicKernelProductMeasure (M : FiniteIrreducibleModel S) (ell : ℕ) :
    Measure (Fin (2 * ell) → S) :=
  Measure.pi (fun _ : Fin (2 * ell) ↦ M.bjrModel.mu)

private instance cubicKernelProductMeasure_isFinite
    (M : FiniteIrreducibleModel S) (ell : ℕ) :
    IsFiniteMeasure (cubicKernelProductMeasure M ell) := by
  unfold cubicKernelProductMeasure
  infer_instance

/-- Integration over all cubic branch coordinates as a continuous linear
functional on the continuous-function Banach space. -/
def cubicKernelIntegralCLM (M : FiniteIrreducibleModel S) (ell : ℕ) :
    C((Fin (2 * ell) → S), ℂ) →L[ℂ] ℂ :=
  (MeasureTheory.L1.integralCLM'
      (α := Fin (2 * ell) → S) (E := ℂ)
      (μ := cubicKernelProductMeasure M ell) ℂ).comp
    (ContinuousMap.toLp 1 (cubicKernelProductMeasure M ell) ℂ)

theorem cubicKernelIntegralCLM_apply
    (M : FiniteIrreducibleModel S) (ell : ℕ)
    (f : C((Fin (2 * ell) → S), ℂ)) :
    cubicKernelIntegralCLM M ell f =
      ∫ x : Fin (2 * ell) → S, f x ∂cubicKernelProductMeasure M ell := by
  unfold cubicKernelIntegralCLM
  rw [ContinuousLinearMap.comp_apply, ← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  exact ContinuousMap.coeFn_toLp
    (p := 1) (μ := cubicKernelProductMeasure M ell) (𝕜 := ℂ) f

/-- Integrated pole-removed amplitude of one fixed labelled cubic kernel. -/
def cubicKernelIntegratedNormalizedAmplitude
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  cubicKernelIntegralCLM M ell
    (cubicKernelNormalizedIntegrandFunction M hM K q)

/-- The integrated normalized amplitude is jointly analytic because it is
the continuous linear image of a continuous-function-valued analytic map. -/
theorem cubicKernelIntegratedNormalizedAmplitude_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    AnalyticAt ℂ (cubicKernelIntegratedNormalizedAmplitude M hM K)
      (0, 0) :=
  (cubicKernelIntegralCLM M ell).analyticAt _ |>.comp
    (cubicKernelNormalizedIntegrandFunction_analytic M hM K)

/-- Integral of the unrestricted branch-profile/resolvent product. -/
def cubicKernelIntegratedResolventProduct
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  cubicKernelIntegralCLM M ell
    (cubicKernelResolventIntegrandFunction M hM K q)

/-- On the punctured fold germ, the integrated analytic amplitude is exactly
`X ^ (3 * ell)` times the integrated unrestricted resolvent product. -/
theorem cubicKernelIntegratedNormalizedAmplitude_eq_pow_mul
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cubicKernelIntegratedNormalizedAmplitude M hM K q =
        q.2 ^ (3 * ell) *
          cubicKernelIntegratedResolventProduct M hM K q := by
  filter_upwards
    [cubicKernelNormalizedIntegrandFunction_eq_pow_smul M hM K] with q hq
  intro hX
  unfold cubicKernelIntegratedNormalizedAmplitude
    cubicKernelIntegratedResolventProduct
  rw [hq hX, map_smul]
  simp only [smul_eq_mul]

/-- At the joint base point, integration leaves the exact finite residue
product as the leading cubic amplitude. -/
theorem cubicKernelIntegratedNormalizedAmplitude_base
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    cubicKernelIntegratedNormalizedAmplitude M hM K (0, 0) =
      ∫ x : Fin (2 * ell) → S,
        ∏ e : Fin (3 * ell),
          CKRA_MPR.residueKernel M hM 0
            (x (cubicKernelOrderedEndpoints K.graph e).1,
              x (cubicKernelOrderedEndpoints K.graph e).2)
        ∂cubicKernelProductMeasure M ell := by
  rw [cubicKernelIntegratedNormalizedAmplitude,
    cubicKernelIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [cubicKernelNormalizedIntegrandFunction_apply,
    cubicKernelNormalizedResolventIntegrand_base]

/-- The integrated leading amplitude with every frozen residue replaced by
its explicit Perron rank-one value. -/
theorem cubicKernelIntegratedNormalizedAmplitude_base_explicit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    cubicKernelIntegratedNormalizedAmplitude M hM K (0, 0) =
      ∫ x : Fin (2 * ell) → S,
        ∏ e : Fin (3 * ell),
          M.complexPerronFunction hM
              (x (cubicKernelOrderedEndpoints K.graph e).1) *
            M.complexPerronFunction hM
              (x (cubicKernelOrderedEndpoints K.graph e).2) /
            (Real.sqrt (2 * M.beta hM) : ℂ)
        ∂cubicKernelProductMeasure M ell := by
  rw [cubicKernelIntegratedNormalizedAmplitude_base]
  apply integral_congr_ae
  filter_upwards [] with x
  apply Finset.prod_congr rfl
  intro e _
  exact CKRA_MPR.residueKernel_base M hM _ _

end PerronWright.FiniteIrreducibleKernelAmplitude


