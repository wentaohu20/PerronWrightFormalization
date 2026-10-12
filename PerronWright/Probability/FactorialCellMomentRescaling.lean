import PerronWright.Probability.CompactSizeCellFactorialLimits
import PerronWright.Probability.FactorialDensityNormalization
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Literal size dilation of the density cell moments

The positive coordinate dilation transports the entire labelled cell
integral, including its finite-dimensional Jacobian. No process law or
moment identification is supplied as an interface.
-/

open MeasureTheory Set
open scoped Classical BigOperators Real Pointwise
noncomputable section

namespace PerronWright.FactorialCellMomentRescaling

open CompactSizeCellFactorialLimits SizeCellIndicators CriticalFloorWindow
open ComponentWindowMixedFactorials FactorialDensity
open FinitePointMeasureMixedFactorials

private theorem scaled_window (n : ℕ) (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    c • sizeWindow n a b = sizeWindow n (c*a) (c*b) := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  simp only [sizeWindow,Set.mem_Icc,Pi.le_def,Pi.smul_apply,smul_eq_mul]
  simp only [← div_eq_inv_mul, le_div_iff₀ hc, div_le_iff₀ hc]
  simp only [mul_comm]

theorem cellMomentMass_rescaling {D : Type*} [Fintype D]
    (alpha lambda a b : ℝ) {c : ℝ} (hc : 0 < c) (ha : 0 < a)
    (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ) :
    cellMomentMass alpha (c^3) lambda a b R J S q =
      cellMomentMass 1 1 (alpha*lambda/c^2) (c*a) (c*b) R
        (fun i ↦ (fun z : ℝ ↦ z/c) ⁻¹' J i) S q := by
  unfold cellMomentMass
  apply Finset.sum_congr rfl
  intro r _
  let n := ∑ i, q i
  let F : (Fin n → ℝ) → ℝ := fun y ↦
    cellWeight (fun j ↦ (fun z : ℝ ↦ z/c) ⁻¹' J (label q j)) y *
      density 1 1 (alpha*lambda/c^2) y r
  have he (x : Fin n → ℝ) (hx : x ∈ sizeWindow n a b) :
      cellWeight (fun j ↦ J (label q j)) x * density alpha (c^3) lambda x r =
        c^n * F (c • x) := by
    have hp : ∀ i, 0 < x i := fun i ↦ ha.trans_le (hx.1 i)
    rw [density_rescaling alpha lambda hc x r hp]
    have hw : cellWeight (fun j ↦ (fun z : ℝ ↦ z/c) ⁻¹' J (label q j)) (c • x) =
        cellWeight (fun j ↦ J (label q j)) x := by
      simp only [cellWeight_eq,Pi.smul_apply,smul_eq_mul,Set.mem_preimage,
        mul_div_cancel_left₀ _ hc.ne']
    dsimp only [F]
    rw [hw]
    change _ = c^n * (cellWeight (fun j ↦ J (label q j)) x *
      density 1 1 (alpha*lambda/c^2) (fun i ↦ c*x i) r)
    ring
  calc
    _ = ∫ x in sizeWindow n a b, c^n * F (c • x) :=
      setIntegral_congr_fun measurableSet_Icc he
    _ = c^n * (c^n)⁻¹ * ∫ y in sizeWindow n (c*a) (c*b), F y := by
      rw [integral_const_mul,Measure.setIntegral_comp_smul_of_pos volume F
        (sizeWindow n a b) hc,scaled_window n a b hc]
      simp only [Module.finrank_pi,Fintype.card_fin,smul_eq_mul,mul_assoc]
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero n hc.ne'),one_mul]

theorem cellMomentMass_starred_normalization {D : Type*} [Fintype D]
    (alpha lambda a b : ℝ) {beta : ℝ} (hbeta : 0 < beta) (ha : 0 < a)
    (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ) :
    cellMomentMass alpha beta lambda a b R J S q =
      cellMomentMass 1 1 (alpha*beta^(-2/3 : ℝ)*lambda)
        (beta^(1/3 : ℝ)*a) (beta^(1/3 : ℝ)*b) R
        (fun i ↦ (fun z : ℝ ↦ z/beta^(1/3 : ℝ)) ⁻¹' J i) S q := by
  have hc : 0 < beta^(1/3 : ℝ) := Real.rpow_pos_of_pos hbeta _
  have hl : alpha*lambda/(beta^(1/3 : ℝ))^2 = alpha*beta^(-2/3 : ℝ)*lambda := by
    rw [beta_cubeRoot_square hbeta]
    have he : (-2/3 : ℝ) = -(2/3 : ℝ) := by ring
    rw [he,Real.rpow_neg hbeta.le,div_eq_mul_inv]
    ring
  simpa only [beta_cubeRoot_cube hbeta,hl] using
    cellMomentMass_rescaling alpha lambda a b hc ha R J S q

end PerronWright.FactorialCellMomentRescaling
