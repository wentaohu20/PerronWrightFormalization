import PerronWright.Probability.BrownianPathLaw
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Genuine time-space scaling of the constructed Brownian path law

The explicit continuous path dilation is measurable. Brownian scaling
follows from the proved Gaussian covariance construction in mathlib,
and finite-projective uniqueness plus the rational Borel embedding
identifies its whole compact-open path law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPathDilationLaw

open BrownianPathLaw BrownianGaussianSkeleton

def dilatePath (T : ℝ≥0) (c : ℝ) (f : Path) : Path :=
  ⟨fun t ↦ c*f (t/T),((continuous_path f).comp (continuous_id.div_const T)).const_mul c⟩

theorem measurable_dilatePath (T : ℝ≥0) (c : ℝ) : Measurable (dilatePath T c) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦ c*f (rationalTimeReal q/T))
  exact measurable_pi_lambda _ (fun q ↦ (continuous_eval _).measurable.const_mul c)

def brownianDilation (T : ℝ≥0) : Path → Path := dilatePath T (Real.sqrt T)

theorem measurable_brownianDilation (T : ℝ≥0) : Measurable (brownianDilation T) :=
  measurable_dilatePath T _

theorem brownianDilation_isBrownian (T : ℝ≥0) (hT : 0 < T) :
    IsBrownianReal (fun t f ↦ brownianDilation T f t) pathLaw := by
  have h := isBrownian_pathLaw.smul (c := T⁻¹) (inv_ne_zero (ne_of_gt hT))
  convert h using 1
  funext t f
  change Real.sqrt (T : ℝ)*f (t/T) = (Real.sqrt (↑(T⁻¹) : ℝ))⁻¹*f (T⁻¹*t)
  rw [NNReal.coe_inv,Real.sqrt_inv,inv_inv]
  simp only [div_eq_mul_inv,mul_comm]

theorem indexed_brownianDilation_law (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (fun f : Path ↦ fun t : ℝ≥0 ↦ brownianDilation T f t) =
      pathLaw.map (fun f : Path ↦ fun t : ℝ≥0 ↦ f t) := by
  let X : ℝ≥0 → Path → ℝ := fun t f ↦ brownianDilation T f t
  let Y : ℝ≥0 → Path → ℝ := fun t f ↦ f t
  have hm : Measurable (fun f : Path ↦ fun t ↦ X t f) :=
    measurable_pi_lambda _ (fun t ↦ (continuous_eval t).measurable.comp (measurable_brownianDilation T))
  have hm' : Measurable (fun f : Path ↦ fun t ↦ Y t f) :=
    measurable_pi_lambda _ (fun t ↦ (continuous_eval t).measurable)
  have hx := isProjectiveLimit_map (X := X) (P := pathLaw) hm.aemeasurable
  have hy := isProjectiveLimit_map (X := Y) (P := pathLaw) hm'.aemeasurable
  have he (I : Finset ℝ≥0) : pathLaw.map (fun f ↦ I.restrict (X · f)) =
      pathLaw.map (fun f ↦ I.restrict (Y · f)) :=
    ((brownianDilation_isBrownian T hT).toIsPreBrownianReal.hasLaw I).map_eq.trans
      (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw I).map_eq.symm
  simp only [he] at hx
  exact hx.unique hy

theorem pathLaw_brownianDilation (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (brownianDilation T) = pathLaw := by
  let R : (ℝ≥0 → ℝ) → RationalTime → ℝ := fun x q ↦ x (rationalTimeReal q)
  have hmR : Measurable R := measurable_pi_lambda _ (fun q ↦ measurable_pi_apply _)
  have hmX : Measurable (fun f : Path ↦ fun t : ℝ≥0 ↦ brownianDilation T f t) := by
    apply measurable_pi_lambda
    intro t
    exact (continuous_eval t).measurable.comp (measurable_brownianDilation T)
  have hmY : Measurable (fun f : Path ↦ fun t : ℝ≥0 ↦ f t) :=
    measurable_pi_lambda _ (fun t ↦ (continuous_eval t).measurable)
  have h := congrArg (Measure.map R) (indexed_brownianDilation_law T hT)
  rw [Measure.map_map hmR hmX,Measure.map_map hmR hmY] at h
  apply rationalEval_measurableEmbedding.map_injective
  rw [Measure.map_map continuous_rationalEval.measurable (measurable_brownianDilation T)]
  exact h

end PerronWright.BrownianPathDilationLaw
