import PerronWright.Probability.BrownianKilledBoundaryEntrance
import PerronWright.Probability.BrownianPositiveKilledKernel
import Mathlib.Topology.Piecewise
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Continuity of the actual killed endpoint density in its exit point

These are analytic properties of the already identified actual killed
Brownian density, including the absorbing boundary. They allow an
endpoint-a.e. bridge disintegration to be identified at every endpoint.
No conditioned bridge or excursion identity is supplied as a hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeFiniteDimensionalDensity

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance

theorem continuous_gaussianPDFReal_exit (a : ℝ) (T : ℝ≥0) :
    Continuous (gaussianPDFReal a T) := by
  unfold gaussianPDFReal
  fun_prop

theorem gaussianPDFReal_reflect_zero (a : ℝ) (T : ℝ≥0) :
    gaussianPDFReal a T 0 = gaussianPDFReal (-a) T 0 := by
  simp only [gaussianPDFReal,zero_sub,sub_neg_eq_add,zero_add,neg_sq]

theorem continuous_densityReal_exit (a : ℝ) (T : ℝ≥0) :
    Continuous (densityReal a T) := by
  apply ((continuous_gaussianPDFReal_exit a T).sub
    (continuous_gaussianPDFReal_exit (-a) T)).if ?_ continuous_const
  intro y hy
  change y ∈ frontier (Ioi (0 : ℝ)) at hy
  have he : y = 0 := by simpa only [frontier_Ioi,mem_singleton_iff] using hy
  subst y
  exact sub_eq_zero.mpr (gaussianPDFReal_reflect_zero a T)

theorem continuous_density_exit (a : ℝ) (T : ℝ≥0) : Continuous (density a T) :=
  ENNReal.continuous_ofReal.comp (continuous_densityReal_exit a T)

theorem density_le_prefactor (a : ℝ) (T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    density a T y ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹) := by
  apply ENNReal.ofReal_le_ofReal
  by_cases hy : 0 < y
  · simp only [densityReal,Set.indicator,mem_Ioi,if_pos hy]
    exact (sub_le_self _ (gaussianPDFReal_nonneg (-a) T y)).trans
      (gaussianPDFReal_le_prefactor a T hT y)
  · simp only [densityReal,Set.indicator,mem_Ioi,if_neg hy]
    positivity

theorem continuous_last_kernel_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    Continuous (fun z : ℝ ↦ ∫⁻ x, density x T (z+a) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro z
  apply tendsto_lintegral_filter_of_dominated_convergence
    (μ := μ) (F := fun w x : ℝ ↦ density x T (w+a))
    (f := fun x : ℝ ↦ density x T (z+a))
    (fun _ : ℝ ↦ ENNReal.ofReal ((Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹))
  · apply Eventually.of_forall
    intro w
    have hm : Measurable (fun x : ℝ ↦ (x,w+a)) := measurable_id.prodMk measurable_const
    have hc := (BrownianPositiveKilledKernel.measurable_joint_density T).comp hm
    simpa only [Function.comp_def] using hc
  · exact Eventually.of_forall (fun w ↦ Eventually.of_forall
      (fun x ↦ density_le_prefactor x T hT (w+a)))
  · simp only [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ univ)
  · exact Eventually.of_forall (fun x ↦
      ((continuous_density_exit x T).comp (continuous_id.add_const a)).continuousAt)

theorem continuous_exit_ratio (μ : Measure ℝ) [IsFiniteMeasure μ]
    (t T : ℝ≥0) (ht : 0 < t) (hT : 0 < T) (a : ℝ) :
    Continuous (fun z : ℝ ↦ (∫⁻ x, density x t (z+a) ∂μ)/gaussianPDF 0 T z) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hpos : gaussianPDF 0 T z ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
    (gaussianPDFReal_pos 0 T z (ne_of_gt hT))
  have hfin : gaussianPDF 0 T z ≠ ∞ := ENNReal.ofReal_ne_top
  exact ENNReal.Tendsto.div (continuous_last_kernel_integral μ t ht a).continuousAt
    (Or.inr hpos) (ENNReal.continuous_ofReal.comp
      (continuous_gaussianPDFReal_exit 0 T)).continuousAt (Or.inl hfin)

end PerronWright.BrownianPositiveBridgeFiniteDimensionalDensity
