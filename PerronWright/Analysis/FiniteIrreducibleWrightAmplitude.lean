import PerronWright.Analysis.FiniteIrreducibleCubicIntegratedAmplitude
import PerronWright.Enumeration.PositiveSurplusWrightConstant

/-!
# Actual cubic leading amplitude for finite irreducible kernels

Cubic incidence and finite product integration evaluate the actual
pole-removed kernel integral. The exact presentation-multiplicity sum gives
the existing literal finite cubic EGF constant times sqrt(beta)^ell.
This is a proved amplitude identity, not yet coefficient-transfer asymptotics.
-/
open MeasureTheory PerronWright
open scoped Classical Topology BigOperators
noncomputable section
namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore
variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Exact evaluation of the residue integral -/

/-- Pointwise, the product of all frozen edge residues is a vertex-cube
product divided by the common edge normalization to the `3 * ell` power. -/
theorem cubicKernelResidueProduct_eq_vertexCubes
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    (∏ e : Fin (3 * ell),
        CKRA_MPR.residueKernel M hM 0
          (x (cubicKernelOrderedEndpoints K.graph e).1,
            x (cubicKernelOrderedEndpoints K.graph e).2)) =
      (∏ v : Fin (2 * ell),
          M.complexPerronFunction hM (x v) ^ 3) /
        (Real.sqrt (2 * M.beta hM) : ℂ) ^ (3 * ell) := by
  simp_rw [CKRA_MPR.residueKernel_base]
  rw [Finset.prod_div_distrib]
  have hprod := cubicKernel_orderedEndpoint_product K
    (fun v ↦ M.complexPerronFunction hM (x v))
  rw [hprod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The integral of the cube of the complex Perron function is the cubic
Perron scale `beta`. -/
theorem integral_complexPerronFunction_cube_eq_beta
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    (∫ s : S, M.complexPerronFunction hM s ^ 3 ∂M.bjrModel.mu) =
      (M.beta hM : ℂ) := by
  rw [FiniteIrreducibleModel.bjrModel_mu, M.integral_measure]
  simp only [Complex.real_smul, FiniteIrreducibleModel.complexPerronFunction_apply,
    FiniteIrreducibleModel.beta, FiniteIrreducibleModel.average,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]

/-- Finite product Fubini for the `2 * ell` cubic branch coordinates. -/
theorem integral_cubicPerronVertexProduct_eq_beta_pow
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) :
    (∫ x : Fin (2 * ell) → S,
        ∏ v : Fin (2 * ell),
          M.complexPerronFunction hM (x v) ^ 3
        ∂cubicKernelProductMeasure M ell) =
      (M.beta hM : ℂ) ^ (2 * ell) := by
  unfold cubicKernelProductMeasure
  calc
    _ = ∏ _v : Fin (2 * ell),
          ∫ s : S, M.complexPerronFunction hM s ^ 3 ∂M.bjrModel.mu := by
      exact integral_fintype_prod_eq_prod
        (fun (_v : Fin (2 * ell)) (s : S) ↦
          M.complexPerronFunction hM s ^ 3)
    _ = ∏ _v : Fin (2 * ell), (M.beta hM : ℂ) := by
      apply Finset.prod_congr rfl
      intro v _
      exact integral_complexPerronFunction_cube_eq_beta M hM
    _ = (M.beta hM : ℂ) ^ (2 * ell) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Closed form for the base-point integral of every fixed labelled cubic
kernel.  In particular, this leading scalar is independent of the kernel's
loop and parallel-edge pattern. -/
theorem cubicKernelIntegratedNormalizedAmplitude_base_closedForm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    cubicKernelIntegratedNormalizedAmplitude M hM K (0, 0) =
      (M.beta hM : ℂ) ^ (2 * ell) /
        (Real.sqrt (2 * M.beta hM) : ℂ) ^ (3 * ell) := by
  rw [cubicKernelIntegratedNormalizedAmplitude_base]
  calc
    (∫ x : Fin (2 * ell) → S,
        ∏ e : Fin (3 * ell),
          CKRA_MPR.residueKernel M hM 0
            (x (cubicKernelOrderedEndpoints K.graph e).1,
              x (cubicKernelOrderedEndpoints K.graph e).2)
        ∂cubicKernelProductMeasure M ell) =
      ∫ x : Fin (2 * ell) → S,
        (∏ v : Fin (2 * ell),
            M.complexPerronFunction hM (x v) ^ 3) /
          (Real.sqrt (2 * M.beta hM) : ℂ) ^ (3 * ell)
        ∂cubicKernelProductMeasure M ell := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact cubicKernelResidueProduct_eq_vertexCubes M hM K x
    _ = (∫ x : Fin (2 * ell) → S,
          ∏ v : Fin (2 * ell),
            M.complexPerronFunction hM (x v) ^ 3
          ∂cubicKernelProductMeasure M ell) /
        (Real.sqrt (2 * M.beta hM) : ℂ) ^ (3 * ell) := by
      simp only [div_eq_mul_inv]
      rw [integral_mul_const]
    _ = (M.beta hM : ℂ) ^ (2 * ell) /
        (Real.sqrt (2 * M.beta hM) : ℂ) ^ (3 * ell) := by
      rw [integral_cubicPerronVertexProduct_eq_beta_pow]

/-- The total leading cubic amplitude, with exactly the inverse global
presentation multiplicity used by the finite regrouping theorem. -/
def positiveSurplusCubicLeadingAmplitude
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedNormalizedAmplitude M hM K (0, 0)

/-- Before the harmless square-root simplification, the leading cubic sum is
the exact inverse-multiplicity kernel sum times the base-point integral. -/
theorem positiveSurplusCubicLeadingAmplitude_exact
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) :
    positiveSurplusCubicLeadingAmplitude M hM ell =
      (letI := labelledConnectedCubicKernelFintype ell
       ∑ K : LabelledConnectedCubicKernel ell,
        labelledCubicKernelInverseMultiplicity K) *
      ((M.beta hM : ℂ) ^ (2 * ell) /
        (Real.sqrt (2 * M.beta hM) : ℂ) ^ (3 * ell)) := by
  unfold positiveSurplusCubicLeadingAmplitude
  simp_rw [cubicKernelIntegratedNormalizedAmplitude_base_closedForm]
  rw [Finset.sum_mul]

private theorem positive_power_div_sqrt_power
    (b : ℝ) (hb : 0 < b) (n : ℕ) :
    b ^ (2 * n) / (Real.sqrt (2 * b)) ^ (3 * n) =
      ((Real.sqrt 2) ^ (3 * n))⁻¹ * (Real.sqrt b) ^ n := by
  have hsb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hsb0 : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
  have hsqrtMul : Real.sqrt (2 * b) = Real.sqrt 2 * Real.sqrt b := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hnum : b ^ (2 * n) = (Real.sqrt b) ^ (4 * n) := by
    calc
      b ^ (2 * n) = ((Real.sqrt b) ^ 2) ^ (2 * n) := by rw [hsb]
      _ = (Real.sqrt b) ^ (4 * n) := by
        rw [← pow_mul]
        congr 1
        omega
  have hden : (Real.sqrt (2 * b)) ^ (3 * n) =
      (Real.sqrt 2) ^ (3 * n) * (Real.sqrt b) ^ (3 * n) := by
    rw [hsqrtMul, mul_pow]
  have hratio :
      (Real.sqrt b) ^ (4 * n) / (Real.sqrt b) ^ (3 * n) =
        (Real.sqrt b) ^ n := by
    rw [div_eq_mul_inv,
      ← pow_sub₀ _ hsb0 (by omega : 3 * n ≤ 4 * n)]
    congr 1
    omega
  rw [hnum, hden]
  calc
    (Real.sqrt b) ^ (4 * n) /
          ((Real.sqrt 2) ^ (3 * n) * (Real.sqrt b) ^ (3 * n)) =
        ((Real.sqrt 2) ^ (3 * n))⁻¹ *
          ((Real.sqrt b) ^ (4 * n) / (Real.sqrt b) ^ (3 * n)) := by
      rw [div_eq_mul_inv, mul_inv_rev, div_eq_mul_inv]
      ring
    _ = ((Real.sqrt 2) ^ (3 * n))⁻¹ * (Real.sqrt b) ^ n := by
      rw [hratio]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- The cubic Perron scale in the base integral is precisely one factor
`sqrt beta` for each unit of surplus, after extracting the universal
`sqrt 2` edge normalization. -/
theorem cubicPerronScaleFactor_eq_sqrtBeta_pow
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) :
    (M.beta hM : ℂ) ^ (2 * ell) /
        (Real.sqrt (2 * M.beta hM) : ℂ) ^ (3 * ell) =
      ((Real.sqrt 2 : ℂ) ^ (3 * ell))⁻¹ *
        (Real.sqrt (M.beta hM) : ℂ) ^ ell := by
  exact_mod_cast positive_power_div_sqrt_power
    (M.beta hM) (M.beta_pos hM) ell

/-- The leading cubic-kernel EGF sum is the finite cubic EGF constant times
the exact model-dependent Perron factor `sqrt(beta) ^ ell`.  The Gamma
transfer factor entering the physical Wright constant is deliberately not
part of this base-point identity. -/
theorem positiveSurplusCubicLeadingAmplitude_eq_egfConstant
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) :
    positiveSurplusCubicLeadingAmplitude M hM ell =
      positiveSurplusCubicEGFConstant ell *
        (Real.sqrt (M.beta hM) : ℂ) ^ ell := by
  rw [positiveSurplusCubicLeadingAmplitude_exact,
    cubicPerronScaleFactor_eq_sqrtBeta_pow]
  unfold positiveSurplusCubicEGFConstant
  ring

/-! ## Finite analytic cubic-kernel sum -/

/-- Exact finite sum of all integrated pole-removed cubic-kernel amplitudes,
with the inverse global presentation multiplicity of the existing
regrouping theorem. -/
def positiveSurplusCubicIntegratedAmplitude
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedNormalizedAmplitude M hM K q

/-- The finite cubic-kernel sum is jointly analytic in the field and fold
coordinate. -/
theorem positiveSurplusCubicIntegratedAmplitude_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) :
    AnalyticAt ℂ (positiveSurplusCubicIntegratedAmplitude M hM ell)
      (0, 0) := by
  let _ := labelledConnectedCubicKernelFintype ell
  unfold positiveSurplusCubicIntegratedAmplitude
  let F : LabelledConnectedCubicKernel ell →
      (C(S, ℂ) × ℂ → ℂ) := fun K q ↦
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedNormalizedAmplitude M hM K q
  change AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q) (0, 0)
  have hsum : AnalyticAt ℂ (∑ K, F K) (0, 0) := by
    apply Finset.analyticAt_sum Finset.univ
    intro K _
    exact analyticAt_const.mul
      (cubicKernelIntegratedNormalizedAmplitude_analytic M hM K)
  have hfun : (∑ K, F K) =
      (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q) := by
    funext q
    exact Fintype.sum_apply q F
  rw [← hfun]
  exact hsum

/-- At the joint base point, the finite analytic sum has the exact Wright
constant value. -/
theorem positiveSurplusCubicIntegratedAmplitude_base
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) :
    positiveSurplusCubicIntegratedAmplitude M hM ell (0, 0) =
      positiveSurplusCubicEGFConstant ell *
        (Real.sqrt (M.beta hM) : ℂ) ^ ell := by
  change positiveSurplusCubicLeadingAmplitude M hM ell = _
  exact positiveSurplusCubicLeadingAmplitude_eq_egfConstant M hM ell

/-! ## Punctured identity with the unrestricted resolvent sum -/

/-- Exact finite inverse-multiplicity sum of the unrestricted integrated
cubic path-resolvent products. -/
def positiveSurplusCubicIntegratedResolventSum
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedResolventProduct M hM K q

/-- On one common punctured neighborhood (common because the kernel type is
finite), the analytic cubic sum is exactly `X ^ (3 * ell)` times the finite
unrestricted resolvent sum. -/
theorem positiveSurplusCubicIntegratedAmplitude_eq_pow_mul_resolventSum
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      positiveSurplusCubicIntegratedAmplitude M hM ell q =
        q.2 ^ (3 * ell) *
          positiveSurplusCubicIntegratedResolventSum M hM ell q := by
  let _ := labelledConnectedCubicKernelFintype ell
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ K : LabelledConnectedCubicKernel ell, q.2 ≠ 0 →
          cubicKernelIntegratedNormalizedAmplitude M hM K q =
            q.2 ^ (3 * ell) *
              cubicKernelIntegratedResolventProduct M hM K q := by
    rw [Filter.eventually_all]
    intro K
    exact cubicKernelIntegratedNormalizedAmplitude_eq_pow_mul M hM K
  filter_upwards [hall] with q hq
  intro hX
  unfold positiveSurplusCubicIntegratedAmplitude
    positiveSurplusCubicIntegratedResolventSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [hq K hX]
  ring


end PerronWright.FiniteIrreducibleKernelAmplitude

