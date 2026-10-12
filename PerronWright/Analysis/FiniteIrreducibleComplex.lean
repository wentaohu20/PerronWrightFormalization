import PerronWright.Model.FiniteIrreducibleBJRBridge
import Mathlib.Data.Complex.BigOperators

/-!
# Genuine complex finite kernel and Perron functional

All actions here are the integral actions of the constructed discrete BJR
data.  Complex fixed-space simplicity follows by real and imaginary parts
from finite irreducibility, without a primitive or B2 assumption.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def complexOperator (M : FiniteIrreducibleModel S) : C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  M.continuousKernel.complexActionCLM M.measure

@[simp] theorem complexOperator_apply (M : FiniteIrreducibleModel S)
    (f : C(S, ℂ)) (a : S) :
    M.complexOperator f a = ∑ b, (M.kernel a b * M.weight b : ℝ) * f b :=
  M.continuous_complexAction_apply f a

theorem complexOperator_re (M : FiniteIrreducibleModel S) (f : C(S, ℂ)) (a : S) :
    (M.complexOperator f a).re = M.action (fun b ↦ (f b).re) a := by
  simp only [complexOperator_apply, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, action, mul_assoc]

theorem complexOperator_im (M : FiniteIrreducibleModel S) (f : C(S, ℂ)) (a : S) :
    (M.complexOperator f a).im = M.action (fun b ↦ (f b).im) a := by
  simp only [complexOperator_apply, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, action, mul_assoc]

def complexPerronFunction (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    C(S, ℂ) := ⟨fun a ↦ (M.perronFunction hcrit a : ℂ), continuous_of_discreteTopology⟩

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexPerronFunction_apply (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (a : S) :
    M.complexPerronFunction hcrit a = (M.perronFunction hcrit a : ℂ) := rfl

theorem complexPerronFunction_fixed (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    M.complexOperator (M.complexPerronFunction hcrit) = M.complexPerronFunction hcrit := by
  ext a
  apply Complex.ext
  · rw [M.complexOperator_re]
    simp only [complexPerronFunction_apply, Complex.ofReal_re]
    exact congrFun (M.perronFunction_fixed hcrit) a
  · rw [M.complexOperator_im]
    simp [action]

theorem complex_fixed_eq_scalar_multiple (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (f : C(S, ℂ)) (hf : M.complexOperator f = f) :
    ∃ c : ℂ, f = c • M.complexPerronFunction hcrit := by
  have hre : M.action (fun a ↦ (f a).re) = fun a ↦ (f a).re := by
    funext a
    rw [← M.complexOperator_re, hf]
  have him : M.action (fun a ↦ (f a).im) = fun a ↦ (f a).im := by
    funext a
    rw [← M.complexOperator_im, hf]
  obtain ⟨a, ha⟩ := M.fixed_function_eq_scalar_multiple hcrit _
    (M.perronFunction_pos hcrit) (M.perronFunction_fixed hcrit) _ hre
  obtain ⟨b, hb⟩ := M.fixed_function_eq_scalar_multiple hcrit _
    (M.perronFunction_pos hcrit) (M.perronFunction_fixed hcrit) _ him
  refine ⟨⟨a, b⟩, ?_⟩
  ext x
  apply Complex.ext
  · simpa only [ContinuousMap.smul_apply, smul_eq_mul, complexPerronFunction_apply,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Pi.smul_apply] using congrFun ha x
  · simpa only [ContinuousMap.smul_apply, smul_eq_mul, complexPerronFunction_apply,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      Pi.smul_apply] using congrFun hb x

def weightedFunctional (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    C(S, ℂ) →L[ℂ] ℂ :=
  ∑ a, ((M.weight a * M.perronFunction hcrit a : ℝ) : ℂ) • ContinuousMap.evalCLM ℂ a

omit [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem weightedFunctional_apply (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (f : C(S, ℂ)) :
    M.weightedFunctional hcrit f =
      ∑ a, (M.weight a * M.perronFunction hcrit a : ℝ) * f a := by
  simp only [weightedFunctional, sum_apply,
    smul_apply, ContinuousMap.evalCLM_apply, smul_eq_mul]

omit [MeasurableSpace S] [BorelSpace S] in
theorem weightedFunctional_perronFunction (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    M.weightedFunctional hcrit (M.complexPerronFunction hcrit) = (M.alpha hcrit : ℂ) := by
  rw [M.weightedFunctional_apply]
  simp only [complexPerronFunction_apply, alpha, average, pow_two,
    Complex.ofReal_sum, Complex.ofReal_mul, mul_assoc]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem perron_left_identity (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) (b : S) :
    ∑ a, M.weight a * M.perronFunction hcrit a * M.kernel a b = M.perronFunction hcrit b := by
  rw [← congrFun (M.perronFunction_fixed hcrit) b]
  change _ = ∑ a, M.kernel b a * M.weight a * M.perronFunction hcrit a
  apply Finset.sum_congr rfl
  intro a _
  rw [M.symmetric a b]
  ring

theorem weightedFunctional_action (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (f : C(S, ℂ)) :
    M.weightedFunctional hcrit (M.complexOperator f) = M.weightedFunctional hcrit f := by
  simp only [weightedFunctional_apply, complexOperator_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    ∑ a, (M.weight a * M.perronFunction hcrit a : ℝ) *
        ((M.kernel a b * M.weight b : ℝ) * f b) =
      ((∑ a, M.weight a * M.perronFunction hcrit a * M.kernel a b : ℝ) : ℂ) *
        (M.weight b : ℂ) * f b := by
      rw [Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      push_cast
      ring
    _ = (M.weight b * M.perronFunction hcrit b : ℝ) * f b := by
      rw [M.perron_left_identity hcrit]
      push_cast
      ring

def normalizedPerronFunctional (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    C(S, ℂ) →L[ℂ] ℂ := (M.alpha hcrit : ℂ)⁻¹ • M.weightedFunctional hcrit

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem normalizedPerronFunctional_perronFunction (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    M.normalizedPerronFunctional hcrit (M.complexPerronFunction hcrit) = 1 := by
  change (M.alpha hcrit : ℂ)⁻¹ *
    M.weightedFunctional hcrit (M.complexPerronFunction hcrit) = 1
  rw [M.weightedFunctional_perronFunction]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (M.alpha_pos hcrit).ne')

theorem normalizedPerronFunctional_action (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (f : C(S, ℂ)) :
    M.normalizedPerronFunctional hcrit (M.complexOperator f) =
      M.normalizedPerronFunctional hcrit f := by
  change (M.alpha hcrit : ℂ)⁻¹ * M.weightedFunctional hcrit (M.complexOperator f) = _
  rw [M.weightedFunctional_action]
  rfl

theorem complex_fixed_eq_perronFunctional_smul (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (f : C(S, ℂ)) (hf : M.complexOperator f = f) :
    f = M.normalizedPerronFunctional hcrit f • M.complexPerronFunction hcrit := by
  obtain ⟨c, hc⟩ := M.complex_fixed_eq_scalar_multiple hcrit f hf
  rw [hc, map_smul, M.normalizedPerronFunctional_perronFunction, smul_eq_mul, mul_one]

end PerronWright.FiniteIrreducibleModel
