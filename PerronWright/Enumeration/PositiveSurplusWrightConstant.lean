import PerronWright.Enumeration.CubicKernelIntegratedResolventAmplitude
import PerronWright.Enumeration.CubicPresentationProfileRegroup
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The positive-surplus cubic EGF and Wright constants

This file evaluates the joint-base-point integral of the normalized
resolvent amplitude of one labelled connected cubic kernel.  Cubic valence
turns the product of the `3 * ell` rank-one edge residues into the product of
the cubes of the Perron function over the `2 * ell` branch coordinates.
Finite product Fubini then gives the exact scalar

`beta ^ (2 * ell) / sqrt (2 * beta) ^ (3 * ell)`.

The finite cubic EGF constant below is not postulated.  It is defined by the
literal finite type of labelled connected cubic multigraphs, with the exact
global presentation multiplicity already established by the regrouping
theory.  Its normalization is therefore

`((2 * ell)! * (3 * ell)! * 2 ^ (# loops))⁻¹`

for each labelled cubic kernel, together with the common residue factor
`sqrt 2 ^ (-(3 * ell))`.  This is the leading amplitude in the exponential
generating function.  Wright's physical constant has in addition the
coefficient-transfer factor `sqrt (2 * pi) / Gamma (3 * ell / 2)`.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Cubic incidence converts edge products into vertex cubes -/

private theorem orderedEndpoints_mul_eq_incidenceProduct
    {v : ℕ} (edge : Sym2 (Fin v)) (f : Fin v → ℂ) :
    f (Sym2.sortEquiv edge).1.1 * f (Sym2.sortEquiv edge).1.2 =
      ∏ x : Fin v,
        f x ^ PerronWright.FiniteMultiGraph.incidence edge x := by
  induction edge using Sym2.inductionOn with
  | _ i j =>
      have hi :
          (∏ x : Fin v, f x ^ (if i = x then 1 else 0)) = f i := by
        calc
          (∏ x : Fin v, f x ^ (if i = x then 1 else 0)) =
              ∏ x : Fin v, if i = x then f x else 1 := by
                apply Finset.prod_congr rfl
                intro x _
                by_cases hix : i = x <;> simp [hix]
          _ = f i := Fintype.prod_ite_eq i f
      have hj :
          (∏ x : Fin v, f x ^ (if j = x then 1 else 0)) = f j := by
        calc
          (∏ x : Fin v, f x ^ (if j = x then 1 else 0)) =
              ∏ x : Fin v, if j = x then f x else 1 := by
                apply Finset.prod_congr rfl
                intro x _
                by_cases hjx : j = x <;> simp [hjx]
          _ = f j := Fintype.prod_ite_eq j f
      have hprod :
          (∏ x : Fin v,
              f x ^ PerronWright.FiniteMultiGraph.incidence s(i,j) x) =
            f i * f j := by
        simp only [PerronWright.FiniteMultiGraph.incidence_mk, pow_add,
          Finset.prod_mul_distrib, hi, hj]
      rcases le_total i j with hij | hji
      · simpa [Sym2.sortEquiv, hij] using hprod.symm
      · simpa [Sym2.sortEquiv, hji, mul_comm] using hprod.symm

/-- The product over both ordered endpoints of every edge is the product of
the corresponding vertex value to its multigraph degree.  Loops are counted
twice on both sides. -/
theorem finiteMultiGraph_orderedEndpoint_product
    {v e : ℕ} (H : PerronWright.FiniteMultiGraph v e)
    (f : Fin v → ℂ) :
    (∏ a : Fin e,
        f (Sym2.sortEquiv (H.endpoints a)).1.1 *
          f (Sym2.sortEquiv (H.endpoints a)).1.2) =
      ∏ x : Fin v, f x ^ H.degree x := by
  calc
    _ = ∏ a : Fin e, ∏ x : Fin v,
          f x ^ PerronWright.FiniteMultiGraph.incidence
            (H.endpoints a) x := by
      apply Finset.prod_congr rfl
      intro a _
      exact orderedEndpoints_mul_eq_incidenceProduct (H.endpoints a) f
    _ = ∏ x : Fin v, ∏ a : Fin e,
          f x ^ PerronWright.FiniteMultiGraph.incidence
            (H.endpoints a) x := by
      rw [Finset.prod_comm]
    _ = ∏ x : Fin v, f x ^ H.degree x := by
      apply Finset.prod_congr rfl
      intro x _
      rw [Finset.prod_pow_eq_pow_sum]
      rfl

/-- For a labelled cubic kernel, the endpoint product is exactly the product
of vertex cubes. -/
theorem cubicKernel_orderedEndpoint_product
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (f : Fin (2 * ell) → ℂ) :
    (∏ e : Fin (3 * ell),
        f (cubicKernelOrderedEndpoints K.graph e).1 *
          f (cubicKernelOrderedEndpoints K.graph e).2) =
      ∏ v : Fin (2 * ell), f v ^ 3 := by
  calc
    _ = ∏ v : Fin (2 * ell), f v ^ K.graph.degree v := by
      simpa only [cubicKernelOrderedEndpoints] using
        finiteMultiGraph_orderedEndpoint_product K.graph f
    _ = ∏ v : Fin (2 * ell), f v ^ 3 := by
      apply Finset.prod_congr rfl
      intro v _
      rw [K.cubic v]

/-! ## Exact evaluation of the residue integral -/

/-- Pointwise, the product of all frozen edge residues is a vertex-cube
product divided by the common edge normalization to the `3 * ell` power. -/
theorem cubicKernelResidueProduct_eq_vertexCubes
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (∫ s : S, M.complexPerronFunction hM s ^ 3 ∂M.mu) =
      (M.beta hM : ℂ) := by
  unfold CompactBJRModel.beta
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [CompactBJRModel.complexPerronFunction_apply,
    Complex.ofReal_pow]

/-- Finite product Fubini for the `2 * ell` cubic branch coordinates. -/
theorem integral_cubicPerronVertexProduct_eq_beta_pow
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    (∫ x : Fin (2 * ell) → S,
        ∏ v : Fin (2 * ell),
          M.complexPerronFunction hM (x v) ^ 3
        ∂cubicKernelProductMeasure M ell) =
      (M.beta hM : ℂ) ^ (2 * ell) := by
  unfold cubicKernelProductMeasure
  calc
    _ = ∏ _v : Fin (2 * ell),
          ∫ s : S, M.complexPerronFunction hM s ^ 3 ∂M.mu := by
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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
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

/-! ## The finite labelled cubic-kernel EGF sum and Wright normalization -/

/-- The exact global presentation multiplicity attached to a labelled cubic
kernel.  This is the intrinsic quantity whose presentation version is
`CubicKernelPresentation.globalMultiplicity`. -/
def labelledCubicKernelGlobalMultiplicity
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) : ℕ :=
  (2 * ell).factorial * (3 * ell).factorial *
    2 ^ Fintype.card (CubicKernelLoopEdge K.graph)

theorem labelledCubicKernelGlobalMultiplicity_pos
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    0 < labelledCubicKernelGlobalMultiplicity K := by
  unfold labelledCubicKernelGlobalMultiplicity
  positivity

/-- The kernel-level formula is literally the global multiplicity used by
the existing presentation-regrouping theorem. -/
@[simp] theorem labelledCubicKernelGlobalMultiplicity_eq_presentation
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    labelledCubicKernelGlobalMultiplicity K =
      CubicKernelPresentation.globalMultiplicity
        (⟨K, D⟩ : CubicKernelPresentation k ell) := by
  rfl

/-- Reciprocal exact global multiplicity, in the scalar field used by the
analytic amplitude. -/
def labelledCubicKernelInverseMultiplicity
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) : ℂ :=
  (labelledCubicKernelGlobalMultiplicity K : ℂ)⁻¹

/-- The positive-surplus cubic EGF leading-amplitude constant, constructed as
a literal finite sum over labelled connected cubic multigraphs.  The
factorials quotient the branch and edge coordinate labels, the loop power
quotients independent loop reversals, and the common square-root power comes
from the frozen path residues. -/
def positiveSurplusCubicEGFConstant (ell : ℕ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ((Real.sqrt 2 : ℂ) ^ (3 * ell))⁻¹ *
    ∑ K : LabelledConnectedCubicKernel ell,
      labelledCubicKernelInverseMultiplicity K

/-- The definition displayed with the full factorial/loop normalization. -/
theorem positiveSurplusCubicEGFConstant_eq_labelledKernelSum (ell : ℕ) :
    positiveSurplusCubicEGFConstant ell =
      ((Real.sqrt 2 : ℂ) ^ (3 * ell))⁻¹ *
        letI := labelledConnectedCubicKernelFintype ell
        ∑ K : LabelledConnectedCubicKernel ell,
          (((2 * ell).factorial * (3 * ell).factorial *
            2 ^ Fintype.card (CubicKernelLoopEdge K.graph) : ℕ) : ℂ)⁻¹ := by
  rfl

/-- Wright's physical positive-surplus constant.  The argument `ell` is the
excess parameter, so this definition represents `w_(ell+1)` and is used in
the positive-surplus regime `0 < ell`.  The Gamma factor is the exact
coefficient-transfer factor for a pole of order `3 * ell / 2`. -/
def positiveSurplusWrightConstant (ell : ℕ) : ℂ :=
  ((Real.sqrt (2 * Real.pi) /
      Real.Gamma (3 * (ell : ℝ) / 2) : ℝ) : ℂ) *
    positiveSurplusCubicEGFConstant ell

/-- The physical Wright constant is the cubic EGF amplitude multiplied by
the universal coefficient-transfer factor. -/
theorem positiveSurplusWrightConstant_eq_transferFactor_mul_egfConstant
    (ell : ℕ) :
    positiveSurplusWrightConstant ell =
      ((Real.sqrt (2 * Real.pi) /
          Real.Gamma (3 * (ell : ℝ) / 2) : ℝ) : ℂ) *
        positiveSurplusCubicEGFConstant ell := by
  rfl

/-- The total leading cubic amplitude, with exactly the inverse global
presentation multiplicity used by the finite regrouping theorem. -/
def positiveSurplusCubicLeadingAmplitude
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedNormalizedAmplitude M hM K (0, 0)

/-- Before the harmless square-root simplification, the leading cubic sum is
the exact inverse-multiplicity kernel sum times the base-point integral. -/
theorem positiveSurplusCubicLeadingAmplitude_exact
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
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

/-- The cubic Perron scale in the base integral is precisely one factor
`sqrt beta` for each unit of surplus, after extracting the universal
`sqrt 2` edge normalization. -/
theorem cubicPerronScaleFactor_eq_sqrtBeta_pow
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    positiveSurplusCubicLeadingAmplitude M hM ell =
      positiveSurplusCubicEGFConstant ell *
        (Real.sqrt (M.beta hM) : ℂ) ^ ell := by
  rw [positiveSurplusCubicLeadingAmplitude_exact,
    cubicPerronScaleFactor_eq_sqrtBeta_pow]
  unfold positiveSurplusCubicEGFConstant
  ring

end PerronWright.GraphCore
