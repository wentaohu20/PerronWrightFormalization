import PerronWright.Probability.BrownianPinnedBridgeArea

/-! # Real exponential tilts of literal continuous Brownian bridge area

This is an actual path measure weighted by the exponential of the
signed continuous bridge integral. Its probability normalization,
Radon--Nikodym density and tilted area law are proved from the preceding
actual Brownian-area law. No positive-excursion area identity is claimed.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPinnedBridgeAreaTilt

open BrownianPathLaw BrownianPinnedBridgeArea

theorem integral_exp_mul_area (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (∫ f, Real.exp (u*area T f) ∂pathLaw) = Real.exp ((T : ℝ)^3*u^2/24) := by
  have h := mgf_gaussianReal (hasLaw_area T hT).map_eq u
  simp only [mgf,zero_mul,zero_add,
    Real.coe_toNNReal _ (by positivity : 0 ≤ (T : ℝ)^3/12)] at h
  convert h using 1
  congr 1
  ring

theorem integrable_exp_mul_area (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Integrable (fun f ↦ Real.exp (u*area T f)) pathLaw := by
  apply mgf_pos_iff.mp
  change 0 < ∫ f, Real.exp (u*area T f) ∂pathLaw
  rw [integral_exp_mul_area T hT u]
  exact Real.exp_pos _

def tiltedAreaLaw (T : ℝ≥0) (u : ℝ) : Measure Path :=
  pathLaw.tilted (fun f ↦ u*area T f)

theorem tiltedAreaLaw_isProbability (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    IsProbabilityMeasure (tiltedAreaLaw T u) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_area T hT u)

theorem tiltedAreaLaw_eq_withDensity (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    tiltedAreaLaw T u = pathLaw.withDensity
      (fun f ↦ ENNReal.ofReal (Real.exp (u*area T f-(T : ℝ)^3*u^2/24))) := by
  unfold tiltedAreaLaw Measure.tilted
  rw [integral_exp_mul_area T hT u]
  simp only [Real.exp_sub]

/-- Exact signed continuous area law under a true weighted Brownian
path probability, for every real tilt parameter. -/
theorem hasLaw_area_tilted (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    HasLaw (area T) (gaussianReal ((T : ℝ)^3*u/12)
      (Real.toNNReal ((T : ℝ)^3/12))) (tiltedAreaLaw T u) := by
  let Q := (T : ℝ)^3/12
  have hcoe : (Real.toNNReal ((T : ℝ)^3/12) : ℝ) = (T : ℝ)^3/12 :=
    Real.coe_toNNReal _ (by positivity)
  let Z := Real.exp ((T : ℝ)^3*u^2/24)
  have hX := measurable_area T
  let := tiltedAreaLaw_isProbability T hT u
  refine ⟨hX.aemeasurable,?_⟩
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_apply_real,integral_map hX.aemeasurable (by fun_prop)]
  rw [tiltedAreaLaw,integral_tilted,integral_exp_mul_area T hT u]
  have he : (fun f : Path ↦
      (Real.exp (u*area T f)/Real.exp ((T : ℝ)^3*u^2/24)) •
        Complex.exp ((s : ℂ)*(area T f : ℂ)*Complex.I)) =
      (fun f ↦ (Z : ℂ)⁻¹ *
        Complex.exp (((u : ℂ)+(s : ℂ)*Complex.I)*(area T f : ℂ))) := by
    funext f
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_exp,Z]
    rw [div_eq_mul_inv,
      mul_comm (Complex.exp ((u*area T f : ℝ) : ℂ))
        ((Complex.exp ((((T : ℝ)^3*u^2 : ℝ) : ℂ)/((24 : ℝ) : ℂ)))⁻¹),
      mul_assoc,← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [he,integral_const_mul]
  change (Z : ℂ)⁻¹ * complexMGF (area T) pathLaw ((u : ℂ)+(s : ℂ)*Complex.I) = _
  rw [complexMGF_gaussianReal (hasLaw_area T hT).map_eq,charFun_gaussianReal,hcoe]
  simp only [Complex.ofReal_zero,mul_zero]
  simp only [Z,Complex.ofReal_exp,← Complex.exp_neg,← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

theorem integral_area_tilted (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (∫ f, area T f ∂tiltedAreaLaw T u) = (T : ℝ)^3*u/12 := by
  rw [(hasLaw_area_tilted T hT u).integral_eq,integral_id_gaussianReal]

theorem variance_area_tilted (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Var[area T;tiltedAreaLaw T u] = (T : ℝ)^3/12 := by
  rw [(hasLaw_area_tilted T hT u).variance_eq,variance_id_gaussianReal,
    Real.coe_toNNReal _ (by positivity : 0 ≤ (T : ℝ)^3/12)]

end PerronWright.BrownianPinnedBridgeAreaTilt
