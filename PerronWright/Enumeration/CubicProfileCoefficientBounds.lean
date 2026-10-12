import PerronWright.Enumeration.CubicActualAdmissibleCoefficientBridge
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform bounds for cubic admissible-profile coefficients

For a regular critical compact model, the coefficient carried by a single
oriented kernel edge has a geometric bound on every closed profile ball.
Multiplying over the finitely many branches and kernel edges, and enlarging
the admissible set of length profiles to the full finite antidiagonal, gives
an explicit binomial-geometric bound for the activity-zero cubic profile
coefficient.  Consequently these coefficients are absolutely summable on
every strict subcritical profile ball.
-/

open MeasureTheory PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

namespace MPR

export PerronWright.MarkedPathResolvent
  (pathOperatorParameterCLM)

end MPR

namespace JS

export PerronWright.JointSimpleCycleEGF
  (pathOperator_pow_succ_norm_le)

end JS

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private abbrev PathEnd (S : Type*) [MetricSpace S] [CompactSpace S] :=
  C(S, ℂ) →L[ℂ] C(S, ℂ)

local instance boundsPathEndNormedRing : NormedRing (PathEnd S) := inferInstance
local instance boundsPathEndSeminormedRing : SeminormedRing (PathEnd S) :=
  NormedRing.toSeminormedRing
@[reducible] local instance boundsPathEndNormedAddCommGroup :
    NormedAddCommGroup (PathEnd S) :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance boundsPathEndNormedAlgebra : NormedAlgebra ℂ (PathEnd S) := inferInstance
@[reducible] local instance boundsPathEndNormedSpace : NormedSpace ℂ (PathEnd S) :=
  NormedAlgebra.toNormedSpace (PathEnd S)
local instance boundsPathEndNormTopology : TopologicalSpace (PathEnd S) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-! ## One-edge geometric estimate -/

private theorem norm_profilePathEdgeCoefficient_le_operator
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (a b : S) (n : ℕ) :
    ‖profilePathEdgeCoefficient M tau a b n‖ ≤
      ‖M.kernel.toContinuousMap‖ *
        ‖(MPR.pathOperatorParameterCLM M tau) ^ n‖ := by
  unfold profilePathEdgeCoefficient
  calc
    ‖(((MPR.pathOperatorParameterCLM M tau) ^ n)
        (M.kernel.complexColumns b)) a‖ ≤
        ‖((MPR.pathOperatorParameterCLM M tau) ^ n)
          (M.kernel.complexColumns b)‖ :=
      (((MPR.pathOperatorParameterCLM M tau) ^ n)
        (M.kernel.complexColumns b)).norm_coe_le_norm a
    _ ≤ ‖(MPR.pathOperatorParameterCLM M tau) ^ n‖ *
          ‖M.kernel.complexColumns b‖ :=
      ((MPR.pathOperatorParameterCLM M tau) ^ n).le_opNorm _
    _ ≤ ‖(MPR.pathOperatorParameterCLM M tau) ^ n‖ *
          ‖M.kernel.toContinuousMap‖ :=
      mul_le_mul_of_nonneg_left (M.kernel.norm_complexColumns_le b)
        (norm_nonneg _)
    _ = ‖M.kernel.toContinuousMap‖ *
          ‖(MPR.pathOperatorParameterCLM M tau) ^ n‖ := by ring

/-- Every one-edge path coefficient has a common geometric bound on every
closed profile ball.  The constant is independent of the endpoints, the
profile, the radius, and the path length. -/
theorem exists_profilePathEdgeCoefficient_geometric_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (tau : C(S, ℂ)) (q : ℝ), 0 ≤ q →
        (∀ x, ‖tau x‖ ≤ q) →
          ∀ (a b : S) (n : ℕ),
            ‖profilePathEdgeCoefficient M tau a b n‖ ≤ B * q ^ n := by
  obtain ⟨m, hm, hmu⟩ := M.perronFunction_uniform_pos hM
  let A : ℝ := ‖M.kernel.complexActionCLM M.mu‖ *
    (‖M.perronFunction hM‖ / m)
  let B : ℝ := ‖M.kernel.toContinuousMap‖ * max 1 A
  refine ⟨B, ?_, ?_⟩
  · dsimp only [B]
    positivity
  · intro tau q hq htau a b n
    have hop := norm_profilePathEdgeCoefficient_le_operator M tau a b n
    cases n with
    | zero =>
        calc
          ‖profilePathEdgeCoefficient M tau a b 0‖ ≤
              ‖M.kernel.toContinuousMap‖ *
                ‖(1 : PathEnd S)‖ := by simpa using hop
          _ ≤ ‖M.kernel.toContinuousMap‖ := by
            change ‖M.kernel.toContinuousMap‖ *
                ‖ContinuousLinearMap.id ℂ C(S, ℂ)‖ ≤
              ‖M.kernel.toContinuousMap‖
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
                (norm_nonneg M.kernel.toContinuousMap)
          _ ≤ B * q ^ 0 := by
            simp only [pow_zero, mul_one]
            dsimp only [B]
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left (le_max_left 1 A)
                (norm_nonneg M.kernel.toContinuousMap)
    | succ n =>
        have hpow := JS.pathOperator_pow_succ_norm_le
          M hM tau q m hq htau hm hmu n
        calc
          ‖profilePathEdgeCoefficient M tau a b (n + 1)‖ ≤
              ‖M.kernel.toContinuousMap‖ *
                ‖(MPR.pathOperatorParameterCLM M tau) ^ (n + 1)‖ := by
            simpa only [Nat.succ_eq_add_one] using hop
          _ ≤ ‖M.kernel.toContinuousMap‖ * (A * q ^ (n + 1)) := by
            apply mul_le_mul_of_nonneg_left _
              (norm_nonneg M.kernel.toContinuousMap)
            simpa only [A] using hpow
          _ ≤ B * q ^ (n + 1) := by
            dsimp only [B]
            have hA : A ≤ max 1 A := le_max_right 1 A
            calc
              ‖M.kernel.toContinuousMap‖ * (A * q ^ (n + 1)) ≤
                  ‖M.kernel.toContinuousMap‖ *
                    (max 1 A * q ^ (n + 1)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hA (pow_nonneg hq _))
                  (norm_nonneg M.kernel.toContinuousMap)
              _ = (‖M.kernel.toContinuousMap‖ * max 1 A) *
                    q ^ (n + 1) := by ring

/-! ## One length profile and its finite antidiagonal -/

private theorem norm_cubicLengthProfileComplexKernelIntegral_le
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell d : ℕ} (K : LabelledConnectedCubicKernel ell)
    (L : CubicKernelLengthProfile (2 * ell + d) ell K.graph)
    (q B : ℝ) (hq : 0 ≤ q) (_hB : 0 ≤ B)
    (htau : ∀ x, ‖tau x‖ ≤ q)
    (hedge : ∀ (a b : S) (n : ℕ),
      ‖profilePathEdgeCoefficient M tau a b n‖ ≤ B * q ^ n) :
    ‖cubicLengthProfileComplexKernelIntegral M tau K L‖ ≤
      B ^ (3 * ell) * q ^ (2 * ell + d) := by
  have htotal : ∑ e : Fin (3 * ell), (L.length e).val = d := by
    have h := L.totalLength
    omega
  have hpoint (x : Fin (2 * ell) → S) :
      ‖(∏ v : Fin (2 * ell), tau (x v)) *
          ∏ e : Fin (3 * ell),
            profilePathEdgeCoefficient M tau
              (x (cubicKernelOrderedEndpoints K.graph e).1)
              (x (cubicKernelOrderedEndpoints K.graph e).2)
              (L.length e).val‖ ≤
        B ^ (3 * ell) * q ^ (2 * ell + d) := by
    have hbranch :
        ‖∏ v : Fin (2 * ell), tau (x v)‖ ≤ q ^ (2 * ell) := by
      calc
        ‖∏ v : Fin (2 * ell), tau (x v)‖ =
            ∏ v : Fin (2 * ell), ‖tau (x v)‖ := by
          simp only [norm_prod]
        _ ≤ ∏ _v : Fin (2 * ell), q := by
          apply Finset.prod_le_prod
          · intro v hv
            exact norm_nonneg _
          · intro v hv
            exact htau (x v)
        _ = q ^ (2 * ell) := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hedges :
        ‖∏ e : Fin (3 * ell),
            profilePathEdgeCoefficient M tau
              (x (cubicKernelOrderedEndpoints K.graph e).1)
              (x (cubicKernelOrderedEndpoints K.graph e).2)
              (L.length e).val‖ ≤
          B ^ (3 * ell) * q ^ d := by
      calc
        ‖∏ e : Fin (3 * ell),
            profilePathEdgeCoefficient M tau
              (x (cubicKernelOrderedEndpoints K.graph e).1)
              (x (cubicKernelOrderedEndpoints K.graph e).2)
              (L.length e).val‖ =
            ∏ e : Fin (3 * ell),
              ‖profilePathEdgeCoefficient M tau
                (x (cubicKernelOrderedEndpoints K.graph e).1)
                (x (cubicKernelOrderedEndpoints K.graph e).2)
                (L.length e).val‖ := by
          simp only [norm_prod]
        _ ≤ ∏ e : Fin (3 * ell),
              (B * q ^ (L.length e).val) := by
          apply Finset.prod_le_prod
          · intro e he
            exact norm_nonneg _
          · intro e he
            exact hedge _ _ _
        _ = B ^ (3 * ell) * q ^ d := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin,
            Finset.prod_pow_eq_pow_sum, htotal]
    rw [norm_mul]
    calc
      ‖∏ v : Fin (2 * ell), tau (x v)‖ *
          ‖∏ e : Fin (3 * ell),
            profilePathEdgeCoefficient M tau
              (x (cubicKernelOrderedEndpoints K.graph e).1)
              (x (cubicKernelOrderedEndpoints K.graph e).2)
              (L.length e).val‖ ≤
          q ^ (2 * ell) * (B ^ (3 * ell) * q ^ d) :=
        mul_le_mul hbranch hedges (norm_nonneg _) (pow_nonneg hq _)
      _ = B ^ (3 * ell) * q ^ (2 * ell + d) := by
        rw [pow_add]
        ring
  unfold cubicLengthProfileComplexKernelIntegral
  calc
    ‖∫ x : Fin (2 * ell) → S,
        (∏ v : Fin (2 * ell), tau (x v)) *
          ∏ e : Fin (3 * ell),
            profilePathEdgeCoefficient M tau
              (x (cubicKernelOrderedEndpoints K.graph e).1)
              (x (cubicKernelOrderedEndpoints K.graph e).2)
              (L.length e).val
        ∂Measure.pi (fun _ : Fin (2 * ell) ↦ M.mu)‖ ≤
      (B ^ (3 * ell) * q ^ (2 * ell + d)) *
        (Measure.pi (fun _ : Fin (2 * ell) ↦ M.mu)).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with x
      exact hpoint x
    _ = B ^ (3 * ell) * q ^ (2 * ell + d) := by simp

private theorem card_cubicKernelLengthProfile_le_choose
    {ell d : ℕ} (hell : 0 < ell)
    (K : LabelledConnectedCubicKernel ell) :
    letI := cubicKernelLengthProfileFintype
      (2 * ell + d) ell K.graph
    Fintype.card (CubicKernelLengthProfile (2 * ell + d) ell K.graph) ≤
      (d + (3 * ell - 1)).choose (3 * ell - 1) := by
  let _ : Fintype (CubicKernelLengthProfile
      (2 * ell + d) ell K.graph) := cubicKernelLengthProfileFintype
    (2 * ell + d) ell K.graph
  calc
    Fintype.card (CubicKernelLengthProfile (2 * ell + d) ell K.graph) =
        Fintype.card
          (CubicKernelAdmissibleLengthAntidiagonal d ell K.graph) :=
      Fintype.card_congr
        (cubicKernelLengthProfileEquivAdmissibleAntidiagonal
          d ell K.graph)
    _ ≤ Fintype.card ↑(Finset.univ.finsuppAntidiag d :
          Finset (Fin (3 * ell) →₀ ℕ)) :=
      Fintype.card_subtype_le _
    _ = (3 * ell + d - 1).choose d := by
      simpa using
        (Finset.card_finsuppAntidiag_nat_eq_choose
          (s := (Finset.univ : Finset (Fin (3 * ell)))) d)
    _ = (d + (3 * ell - 1)).choose (3 * ell - 1) := by
      rw [show 3 * ell + d - 1 = d + (3 * ell - 1) by omega]
      exact Nat.choose_symm_add

/-! ## Coefficient majorant and normal convergence -/

/-- At fixed positive surplus, all activity-zero cubic profile coefficients
on a closed profile ball are bounded by one binomial-geometric majorant.
The constant depends only on the model and the surplus. -/
theorem exists_positiveSurplusCubicAdmissibleProfileCoefficient_norm_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (tau : C(S, ℂ)) (q : ℝ), 0 ≤ q → ‖tau‖ ≤ q →
        ∀ d : ℕ,
          ‖positiveSurplusCubicAdmissibleProfileCoefficient
              M tau ell d‖ ≤
            C * ((d + (3 * ell - 1)).choose (3 * ell - 1) : ℝ) *
              q ^ (2 * ell + d) := by
  classical
  obtain ⟨B, hB, hedge⟩ :=
    exists_profilePathEdgeCoefficient_geometric_bound M hM
  let _ : Fintype (LabelledConnectedCubicKernel ell) :=
    labelledConnectedCubicKernelFintype ell
  let W : ℝ := ∑ K : LabelledConnectedCubicKernel ell,
    ‖labelledCubicKernelInverseMultiplicity K‖
  let C : ℝ := W * B ^ (3 * ell)
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C, W]
    positivity
  · intro tau q hq htau d
    have htau' : ∀ x, ‖tau x‖ ≤ q := fun x ↦
      (tau.norm_coe_le_norm x).trans htau
    have hedge' : ∀ (a b : S) (n : ℕ),
        ‖profilePathEdgeCoefficient M tau a b n‖ ≤ B * q ^ n :=
      hedge tau q hq htau'
    have hchoose (K : LabelledConnectedCubicKernel ell) :
        letI := cubicKernelLengthProfileFintype
          (2 * ell + d) ell K.graph
        (Fintype.card
            (CubicKernelLengthProfile (2 * ell + d) ell K.graph) : ℝ) ≤
          ((d + (3 * ell - 1)).choose (3 * ell - 1) : ℝ) := by
      let _ : Fintype (CubicKernelLengthProfile
          (2 * ell + d) ell K.graph) := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      exact_mod_cast card_cubicKernelLengthProfile_le_choose hell K
    have hkernel (K : LabelledConnectedCubicKernel ell) :
        letI := cubicKernelLengthProfileFintype
          (2 * ell + d) ell K.graph
        ‖∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
            cubicLengthProfileComplexKernelIntegral M tau K L‖ ≤
          ((d + (3 * ell - 1)).choose (3 * ell - 1) : ℝ) *
            (B ^ (3 * ell) * q ^ (2 * ell + d)) := by
      let _ : Fintype (CubicKernelLengthProfile
          (2 * ell + d) ell K.graph) := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      calc
        ‖∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
            cubicLengthProfileComplexKernelIntegral M tau K L‖ ≤
            ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
              ‖cubicLengthProfileComplexKernelIntegral M tau K L‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _L : CubicKernelLengthProfile
              (2 * ell + d) ell K.graph,
              (B ^ (3 * ell) * q ^ (2 * ell + d)) := by
          apply Finset.sum_le_sum
          intro L hL
          exact norm_cubicLengthProfileComplexKernelIntegral_le
            M tau K L q B hq hB htau' hedge'
        _ = (Fintype.card
              (CubicKernelLengthProfile (2 * ell + d) ell K.graph) : ℝ) *
              (B ^ (3 * ell) * q ^ (2 * ell + d)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ((d + (3 * ell - 1)).choose (3 * ell - 1) : ℝ) *
              (B ^ (3 * ell) * q ^ (2 * ell + d)) := by
          exact mul_le_mul_of_nonneg_right (hchoose K)
            (mul_nonneg (pow_nonneg hB _) (pow_nonneg hq _))
    unfold positiveSurplusCubicAdmissibleProfileCoefficient
    let _ : ∀ K : LabelledConnectedCubicKernel ell,
        Fintype (CubicKernelLengthProfile (2 * ell + d) ell K.graph) :=
      fun K ↦ cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
    calc
      ‖∑ K : LabelledConnectedCubicKernel ell,
          labelledCubicKernelInverseMultiplicity K *
            ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
              cubicLengthProfileComplexKernelIntegral M tau K L‖ ≤
          ∑ K : LabelledConnectedCubicKernel ell,
            ‖labelledCubicKernelInverseMultiplicity K *
              ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
                cubicLengthProfileComplexKernelIntegral M tau K L‖ :=
        norm_sum_le _ _
      _ ≤ ∑ K : LabelledConnectedCubicKernel ell,
            ‖labelledCubicKernelInverseMultiplicity K‖ *
              (((d + (3 * ell - 1)).choose (3 * ell - 1) : ℝ) *
                (B ^ (3 * ell) * q ^ (2 * ell + d))) := by
        apply Finset.sum_le_sum
        intro K hK
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hkernel K) (norm_nonneg _)
      _ = (∑ K : LabelledConnectedCubicKernel ell,
              ‖labelledCubicKernelInverseMultiplicity K‖) *
            (((d + (3 * ell - 1)).choose (3 * ell - 1) : ℝ) *
              (B ^ (3 * ell) * q ^ (2 * ell + d))) := by
        rw [Finset.sum_mul]
      _ = C * ((d + (3 * ell - 1)).choose (3 * ell - 1) : ℝ) *
            q ^ (2 * ell + d) := by
        dsimp only [C, W]
        ring

/-- The activity-zero cubic profile coefficients are absolutely summable
on every strict subcritical profile ball. -/
theorem summable_norm_positiveSurplusCubicAdmissibleProfileCoefficient
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell) (tau : C(S, ℂ))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    Summable (fun d : ℕ ↦
      ‖positiveSurplusCubicAdmissibleProfileCoefficient
        M tau ell d‖) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_positiveSurplusCubicAdmissibleProfileCoefficient_norm_bound
      M hM hell
  let k : ℕ := 3 * ell - 1
  have hrnorm : ‖r‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
  have hgeom : Summable (fun d : ℕ ↦
      ((d + k).choose k : ℝ) * r ^ d) :=
    summable_choose_mul_geometric_of_norm_lt_one k hrnorm
  have hmajor : Summable (fun d : ℕ ↦
      C * ((d + k).choose k : ℝ) * r ^ (2 * ell + d)) := by
    have h := hgeom.mul_left (C * r ^ (2 * ell))
    simpa only [pow_add, k, mul_assoc, mul_left_comm, mul_comm] using h
  apply Summable.of_norm_bounded hmajor
  intro d
  rw [Real.norm_eq_abs, abs_norm]
  simpa only [k] using hbound tau r hr htau d

end PerronWright.GraphCore
