import PerronWright.Probability.BrownianPinnedBridgeFiniteLaw
import Mathlib.MeasureTheory.Measure.Tilted

/-! # Exact exponential tilts of the actual Brownian bridge tests

The tilted source below is an actual exponentially weighted Brownian
path measure. Its normalizer and the Gaussian law of the weighted
finite linear test are proved exactly for all real tilt parameters.
This is not a continuous excursion-area tilt or a Wright moment formula.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPinnedBridgeTilt

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeFiniteLaw

variable {ι : Type*} [Fintype ι]

theorem continuous_linearTest (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) :
    Continuous (linearTest T t c) :=
  continuous_finsetSum _ (fun i _ ↦ (continuous_bridge T (t i)).const_mul (c i))

theorem integral_exp_mul_linearTest (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (u : ℝ) :
    (∫ f, Real.exp (u*linearTest T t c f) ∂pathLaw) =
      Real.exp (quadraticVariance T t c * u^2/2) := by
  have h := mgf_gaussianReal (hasLaw_linearTest T hT t ht c).map_eq u
  simpa only [mgf,zero_mul,zero_add,
    Real.coe_toNNReal _ (quadraticVariance_nonneg T hT t ht c)] using h

theorem integrable_exp_mul_linearTest (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (u : ℝ) :
    Integrable (fun f ↦ Real.exp (u*linearTest T t c f)) pathLaw := by
  apply mgf_pos_iff.mp
  change 0 < ∫ f, Real.exp (u*linearTest T t c f) ∂pathLaw
  rw [integral_exp_mul_linearTest T hT t ht c u]
  exact Real.exp_pos _

def tiltedLaw (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) (u : ℝ) : Measure Path :=
  pathLaw.tilted (fun f ↦ u*linearTest T t c f)

theorem tiltedLaw_isProbability (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (u : ℝ) :
    IsProbabilityMeasure (tiltedLaw T t c u) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_linearTest T hT t ht c u)

theorem tiltedLaw_eq_withDensity (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (u : ℝ) :
    tiltedLaw T t c u = pathLaw.withDensity
      (fun f ↦ ENNReal.ofReal (Real.exp (u*linearTest T t c f -
        quadraticVariance T t c * u^2/2))) := by
  unfold tiltedLaw Measure.tilted
  rw [integral_exp_mul_linearTest T hT t ht c u]
  simp only [Real.exp_sub]

/-- The exact finite-test distribution under a true weighted Brownian
source, with no guessed Gaussian or convergence premise. -/
theorem hasLaw_linearTest_tilted (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (u : ℝ) :
    HasLaw (linearTest T t c)
      (gaussianReal (quadraticVariance T t c*u) (Real.toNNReal (quadraticVariance T t c)))
      (tiltedLaw T t c u) := by
  let Q := quadraticVariance T t c
  have hcoe : (Real.toNNReal (quadraticVariance T t c) : ℝ) =
      quadraticVariance T t c :=
    Real.coe_toNNReal _ (quadraticVariance_nonneg T hT t ht c)
  let Z := Real.exp (Q*u^2/2)
  have hX := (continuous_linearTest T t c).measurable
  let := tiltedLaw_isProbability T hT t ht c u
  refine ⟨hX.aemeasurable,?_⟩
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_apply_real,integral_map hX.aemeasurable (by fun_prop)]
  rw [tiltedLaw,integral_tilted]
  rw [integral_exp_mul_linearTest T hT t ht c u]
  have he : (fun f : Path ↦
      (Real.exp (u*linearTest T t c f)/Real.exp (Q*u^2/2)) •
        Complex.exp ((s : ℂ)*(linearTest T t c f : ℂ)*Complex.I)) =
      (fun f ↦ (Z : ℂ)⁻¹ *
        Complex.exp (((u : ℂ)+(s : ℂ)*Complex.I)*(linearTest T t c f : ℂ))) := by
    funext f
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_exp,Z]
    rw [div_eq_mul_inv,
      mul_comm (Complex.exp ((u*linearTest T t c f : ℝ) : ℂ))
        ((Complex.exp (((Q*u^2 : ℝ) : ℂ)/((2 : ℝ) : ℂ)))⁻¹),
      mul_assoc,← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  change (∫ f, (Real.exp (u*linearTest T t c f)/Real.exp (Q*u^2/2)) •
      Complex.exp ((s : ℂ)*(linearTest T t c f : ℂ)*Complex.I) ∂pathLaw) = _
  rw [he,integral_const_mul]
  change (Z : ℂ)⁻¹ * complexMGF (linearTest T t c) pathLaw ((u : ℂ)+(s : ℂ)*Complex.I) = _
  rw [complexMGF_gaussianReal (hasLaw_linearTest T hT t ht c).map_eq,
    charFun_gaussianReal]
  rw [hcoe]
  simp only [Complex.ofReal_zero,mul_zero]
  simp only [Z,Complex.ofReal_exp,← Complex.exp_neg,← Complex.exp_add]
  congr 1
  dsimp only [Q]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

end PerronWright.BrownianPinnedBridgeTilt

