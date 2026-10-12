import PerronWright.Transfer.CartesianOuterArcParam
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Exact Cartesian global contour identity

The correct orientation is

`circleIntegral + localKeyhole + fixedOuterMajorArc = 0`.

The two-term identity `localKeyhole + fixedOuterMajorArc = 0` is false for
the coefficient integrand: the resulting clockwise loop has winding number
`-1` around the origin.  The material below isolates the two genuinely
reusable ingredients for a proof without an abstract contour-deformation
interface:

1. a holomorphic Banach-valued function defines a closed one-form, hence its
   curve integral is invariant under an explicit smooth relative homotopy;
2. the Cartesian Delta-domain is stable under positive radial contraction
   toward the origin (when the cone slope is nonnegative).

The proof is finite and geometric: split
the deformed outer boundary into its six smooth pieces (the major arc and the
five affine keyhole pieces), radially contract each piece to one common inner
circle, apply `holomorphicCurveIntegral_eq_of_contDiffHomotopy`, and cancel the
six radial side paths.  No contour-deformation proposition is assumed.
-/

open Complex MeasureTheory Set Metric Topology
open scoped Interval unitInterval
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex-linear one-form `v ↦ v • G z` associated with a
Banach-valued holomorphic function `G`. -/
def banachHolomorphicOneForm (G : ℂ → E) (z : ℂ) : ℂ →L[ℂ] E :=
  ContinuousLinearMap.smulRightL ℂ ℂ E (1 : ℂ →L[ℂ] ℂ) (G z)

@[simp]
theorem banachHolomorphicOneForm_apply
    (G : ℂ → E) (z v : ℂ) :
    banachHolomorphicOneForm G z v = v • G z := by
  simp [banachHolomorphicOneForm]

/-- The real derivative of `banachHolomorphicOneForm G` written in a form
whose symmetry is algebraic. -/
def banachHolomorphicOneFormFDeriv (G : ℂ → E) (z : ℂ) :
    ℂ →L[ℝ] ℂ →L[ℂ] E :=
  (ContinuousLinearMap.toSpanSingleton ℂ
      ((ContinuousLinearMap.smulRightL ℂ ℂ E
        (1 : ℂ →L[ℂ] ℂ)) (deriv G z))).restrictScalars ℝ

@[simp]
theorem banachHolomorphicOneFormFDeriv_apply
    (G : ℂ → E) (z u v : ℂ) :
    banachHolomorphicOneFormFDeriv G z u v = (v * u) • deriv G z := by
  simp [banachHolomorphicOneFormFDeriv, smul_smul, mul_comm]

theorem banachHolomorphicOneFormFDeriv_symmetric
    (G : ℂ → E) (z u v : ℂ) :
    banachHolomorphicOneFormFDeriv G z u v =
      banachHolomorphicOneFormFDeriv G z v u := by
  simp only [banachHolomorphicOneFormFDeriv_apply]
  rw [mul_comm]

/-- The exact four-side identity for an explicit `C^2` homotopy inside an
open holomorphy domain.  This is a proved wrapper around Mathlib's
square-boundary Poincare theorem, not a contour-deformation assumption. -/
theorem holomorphicCurveIntegral_boundary_eq_of_contDiffHomotopy
    [CompleteSpace E]
    {G : ℂ → E} {U : Set ℂ} {a b c d : ℂ}
    {γ₀ : Path a b} {γ₁ : Path c d}
    (φ : (γ₀ : C(I, ℂ)).Homotopy γ₁)
    (hU : IsOpen U) (hφU : Set.range φ ⊆ U)
    (hG : DifferentiableOn ℂ G U)
    (hφsmooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2)
      (Icc 0 1)) :
    (∫ᶜ z in γ₀, banachHolomorphicOneForm G z) +
        (∫ᶜ z in φ.evalAt 1, banachHolomorphicOneForm G z) =
      (∫ᶜ z in γ₁, banachHolomorphicOneForm G z) +
        (∫ᶜ z in φ.evalAt 0, banachHolomorphicOneForm G z) := by
  let omega : ℂ → ℂ →L[ℂ] E := banachHolomorphicOneForm G
  let domega : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] E :=
    banachHolomorphicOneFormFDeriv G
  have hcompact : IsCompact (Set.range φ) :=
    isCompact_range (map_continuous φ)
  have hderiv : ∀ z ∈ Set.range φ,
      HasFDerivWithinAt omega (domega z) (Set.range φ) z := by
    intro z hz
    have hGz : HasDerivAt G (deriv G z) z :=
      (hG.differentiableAt (hU.mem_nhds (hφU hz))).hasDerivAt
    have hL' : HasDerivAt omega
        ((ContinuousLinearMap.smulRightL ℂ ℂ E
          (1 : ℂ →L[ℂ] ℂ)) (deriv G z)) z :=
      (ContinuousLinearMap.smulRightL ℂ ℂ E
        (1 : ℂ →L[ℂ] ℂ)).hasFDerivAt.comp_hasDerivAt z hGz
    simpa [domega, banachHolomorphicOneFormFDeriv] using
      hL'.hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt
  have hcont : ContinuousOn omega (closure (Set.range φ)) := by
    rw [hcompact.isClosed.closure_eq]
    exact ((ContinuousLinearMap.smulRightL ℂ ℂ E
      (1 : ℂ →L[ℂ] ℂ)).continuous.comp_continuousOn
        ((hG.continuousOn.mono hφU)))
  exact φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    (t := Set.range φ) (ω := omega) (dω := domega)
    (fun _ _ _ _ => mem_range_self _)
    hderiv hcont
    (fun z _ u _ v _ =>
      banachHolomorphicOneFormFDeriv_symmetric G z u v)
    hφsmooth

/-! ### Translation between curve integrals and the existing affine pieces -/

/-- The path underlying `banachAffineBaseIntegral`. -/
def banachAffinePath (p q : ℂ) (a b : ℝ) :
    Path (p + q * (a : ℂ)) (p + q * (b : ℂ)) :=
  Path.segment (p + q * (a : ℂ)) (p + q * (b : ℂ))

/-- The curve integral of the holomorphic one-form along an affine path is
exactly the interval-integral convention already used by the Cartesian
keyhole. -/
theorem curveIntegral_banachAffinePath
    [CompleteSpace E]
    (G : ℂ → E) (p q : ℂ) (a b : ℝ) :
    (∫ᶜ z in banachAffinePath p q a b,
        banachHolomorphicOneForm G z) =
      banachAffineBaseIntegral G p q a b := by
  unfold banachAffinePath
  rw [curveIntegral_segment]
  let f : ℝ → E := fun x => q • G (p + q * (x : ℂ))
  have hpoint (t : ℝ) :
      AffineMap.lineMap (p + q * (a : ℂ)) (p + q * (b : ℂ)) t =
        p + q * ((a + (b - a) * t : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [AffineMap.lineMap_apply, Complex.mul_re, Complex.mul_im] <;>
      ring
  have hdiff :
      p + q * (b : ℂ) - (p + q * (a : ℂ)) =
        ((b - a : ℝ) : ℂ) * q := by
    push_cast
    ring
  have hintegrand (t : ℝ) :
      banachHolomorphicOneForm G
          (AffineMap.lineMap (p + q * (a : ℂ))
            (p + q * (b : ℂ)) t)
          (p + q * (b : ℂ) - (p + q * (a : ℂ))) =
        (b - a) • f (a + (b - a) * t) := by
    rw [hpoint, hdiff, banachHolomorphicOneForm_apply]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp [f, smul_smul]
  simp_rw [hintegrand]
  change (∫ t in (0 : ℝ)..1, (b - a) • f (a + (b - a) * t)) = _
  rw [intervalIntegral.integral_smul]
  simpa [f, banachAffineBaseIntegral] using
    (intervalIntegral.smul_integral_comp_add_mul
      (f := f) (a := (0 : ℝ)) (b := 1) (b - a) a)

/-! ### Radial geometry of the Cartesian Delta-domain -/

/-- Positive contraction toward the origin preserves the Cartesian
Delta-domain.  The nonnegativity of `m` is exactly what makes the excluded
right cone outward closed under radial expansion. -/
theorem positive_scale_mem_cartesianDelta
    {eta m q : ℝ} {z : ℂ}
    (hm : 0 ≤ m) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hz : z ∈ cartesianDelta eta m) :
    (q : ℂ) * z ∈ cartesianDelta eta m := by
  constructor
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    exact (mul_le_of_le_one_left (norm_nonneg z) hq1).trans_lt hz.1
  · intro hcone
    apply hz.2
    have hre : 0 ≤ z.re - 1 := by
      have hs := hcone.1
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.one_re] at hs
      nlinarith
    refine ⟨by simpa only [Complex.sub_re, Complex.one_re] using hre, ?_⟩
    have hs := hcone.2
    have hscaledIm : (((q : ℂ) * z - 1).im) = q * z.im := by simp
    have hscaledRe : (((q : ℂ) * z - 1).re) = q * z.re - 1 := by simp
    rw [hscaledIm, abs_mul, abs_of_pos hq0, hscaledRe] at hs
    have hcompare :
        m * (q * z.re - 1) ≤ q * (m * (z.re - 1)) := by
      nlinarith [mul_nonneg hm (sub_nonneg.mpr hq1)]
    have hqbound : q * |z.im| ≤ q * (m * (z.re - 1)) :=
      hs.trans hcompare
    have him : |z.im| ≤ m * (z.re - 1) :=
      le_of_mul_le_mul_left hqbound hq0
    simpa only [Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, sub_zero] using him

/-- The scalar occurring in a radial homotopy from radius `r` to `z`. -/
def cartesianRadialScale (r s : ℝ) (z : ℂ) : ℝ :=
  (1 - s) * (r / ‖z‖) + s

theorem cartesianRadialScale_pos_le_one
    {r s : ℝ} {z : ℂ}
    (hr : 0 < r) (hrz : r ≤ ‖z‖) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < cartesianRadialScale r s z ∧
      cartesianRadialScale r s z ≤ 1 := by
  have hz : 0 < ‖z‖ := hr.trans_le hrz
  have hratio0 : 0 < r / ‖z‖ := div_pos hr hz
  have hratio1 : r / ‖z‖ ≤ 1 := (div_le_one hz).2 hrz
  constructor
  · dsimp [cartesianRadialScale]
    by_cases hs1 : s = 1
    · simp [hs1]
    · have h1s : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hs1)
      exact add_pos_of_pos_of_nonneg (mul_pos h1s hratio0) hs.1
  · dsimp [cartesianRadialScale]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2)
      (sub_nonneg.mpr hratio1)]

/-- Every point of the explicit radial homotopy remains in the same
Cartesian Delta-domain. -/
theorem cartesianRadialHomotopy_mem
    {eta m r s : ℝ} {z : ℂ}
    (hm : 0 ≤ m) (hr : 0 < r) (hrz : r ≤ ‖z‖)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ cartesianDelta eta m) :
    ((cartesianRadialScale r s z : ℝ) : ℂ) * z ∈
      cartesianDelta eta m := by
  obtain ⟨hq0, hq1⟩ := cartesianRadialScale_pos_le_one hr hrz hs
  exact positive_scale_mem_cartesianDelta hm hq0 hq1 hz

/-! ### A smooth angle lift on the right half-plane

Every one of the five affine pieces of the local keyhole lies in the open
right half-plane (for the detour radii used in the transfer theorem).  On
that half-plane the following elementary lift avoids any appeal to a
general path-lifting theorem.  It is globally smooth because `arctan` is
globally smooth and the real part never vanishes.
-/

/-- The standard real angle lift on the open right half-plane. -/
def cartesianRightHalfAngle (z : ℂ) : ℝ :=
  Real.arctan (z.im / z.re)

/-- On the open right half-plane the elementary `arctan` lift agrees with
the principal complex argument. -/
theorem cartesianRightHalfAngle_eq_arg {z : ℂ} (hz : 0 < z.re) :
    cartesianRightHalfAngle z = Complex.arg z := by
  rw [cartesianRightHalfAngle, ← Complex.tan_arg z]
  exact Real.arctan_tan
    (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz))
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz))

/-- The radial projection of a point in the open right half-plane is the
circle parametrization evaluated at the elementary angle lift. -/
theorem circleMap_cartesianRightHalfAngle
    {r : ℝ} {z : ℂ} (hz : 0 < z.re) :
    circleMap 0 r (cartesianRightHalfAngle z) =
      ((r / ‖z‖ : ℝ) : ℂ) * z := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  rw [cartesianRightHalfAngle_eq_arg hz, circleMap_zero]
  calc
    (r : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) =
        (((r / ‖z‖ : ℝ) : ℂ) *
          (((‖z‖ : ℝ) : ℂ) *
            Complex.exp ((Complex.arg z : ℂ) * Complex.I))) := by
      rw [← mul_assoc, ← ofReal_mul,
        div_mul_cancel₀ r (norm_ne_zero_iff.mpr hz0)]
    _ = (((r / ‖z‖ : ℝ) : ℂ) * z) := by
      rw [Complex.norm_mul_exp_arg_mul_I]

/-- Pointwise smoothness of the elementary angle lift.  The pointwise
form is the useful one for affine keyhole parametrizations, because their
positive-real-part estimate is already available at each parameter. -/
theorem contDiffAt_cartesianRightHalfAngle
    {n : ℕ∞} {z : ℂ} (hz : z.re ≠ 0) :
    ContDiffAt ℝ n cartesianRightHalfAngle z := by
  apply ContDiffAt.arctan
  exact Complex.imCLM.contDiff.contDiffAt.div
    Complex.reCLM.contDiff.contDiffAt hz

/-! ### Circle pullbacks and shifted full periods -/

/-- The Cauchy coefficient integrand pulled back to a circle of arbitrary
positive radius.  Keeping this as a separate definition makes the final
telescoping of the six projected pieces purely one-dimensional. -/
def banachCircleCoefficientPullback
    (F : ℂ → E) (r : ℝ) (n : ℕ) (theta : ℝ) : E :=
  let z := circleMap 0 r theta
  (deriv (circleMap 0 r) theta * z⁻¹ ^ (n + 1)) • F z

theorem banachCircleCoefficientPullback_periodic
    (F : ℂ → E) (r : ℝ) (n : ℕ) :
    Function.Periodic (banachCircleCoefficientPullback F r n)
      (2 * Real.pi) := by
  intro theta
  simp only [banachCircleCoefficientPullback, deriv_circleMap]
  rw [(periodic_circleMap 0 r) theta]

/-- A full circle can be integrated over any angular interval of length
`2*pi`.  This is the final bookkeeping lemma needed after the projected
local pieces telescope from `theta₀` to `-theta₀`, while the projected
major arc runs from `2*pi-theta₀` back to `theta₀`. -/
theorem circleIntegral_eq_shifted_banachCircleCoefficientPullback
    [CompleteSpace E]
    (F : ℂ → E) (r s : ℝ) (n : ℕ) :
    (∮ z in C((0 : ℂ), r), banachCoefficientIntegrand F n z) =
      ∫ theta in s..s + 2 * Real.pi,
        banachCircleCoefficientPullback F r n theta := by
  rw [circleIntegral]
  simp only [banachCoefficientIntegrand, smul_smul]
  change (∫ theta in 0..2 * Real.pi,
      banachCircleCoefficientPullback F r n theta) = _
  have hperiod :=
    banachCircleCoefficientPullback_periodic F r n
  simpa only [zero_add] using
    (hperiod.intervalIntegral_add_eq s 0).symm

/-! ### The explicit radial strip attached to one smooth boundary piece -/

/-- Radial projection of a path onto the circle of radius `r`. -/
def banachRadialProjectionPath
    {a b : ℂ} (gamma : Path a b) (r : ℝ)
    (hgamma0 : ∀ t, gamma t ≠ 0) :
    Path (((r / ‖a‖ : ℝ) : ℂ) * a)
      (((r / ‖b‖ : ℝ) : ℂ) * b) where
  toFun t := ((r / ‖gamma t‖ : ℝ) : ℂ) * gamma t
  continuous_toFun := by
    have hnorm : Continuous (fun t : I ↦ ‖gamma t‖) :=
      continuous_norm.comp gamma.continuous
    have hquot : Continuous (fun t : I ↦ r / ‖gamma t‖) :=
      continuous_const.div hnorm
        (fun t ↦ norm_ne_zero_iff.mpr (hgamma0 t))
    exact (Complex.continuous_ofReal.comp hquot).mul gamma.continuous
  source' := by simp
  target' := by simp

/-- The explicit radial homotopy from the projected path (`s = 0`) to
the original path (`s = 1`).  Its endpoint paths are precisely the two
transverse radial sides which cancel when adjacent boundary pieces are
summed. -/
def banachRadialHomotopy
    {a b : ℂ} (gamma : Path a b) (r : ℝ)
    (hgamma0 : ∀ t, gamma t ≠ 0) :
    ((banachRadialProjectionPath gamma r hgamma0 :
        Path (((r / ‖a‖ : ℝ) : ℂ) * a)
          (((r / ‖b‖ : ℝ) : ℂ) * b)) : C(I, ℂ)).Homotopy
      (gamma : C(I, ℂ)) where
  toFun st :=
    ((cartesianRadialScale r st.1 (gamma st.2) : ℝ) : ℂ) *
      gamma st.2
  continuous_toFun := by
    have hgamma : Continuous (fun st : I × I ↦ gamma st.2) :=
      gamma.continuous.comp continuous_snd
    have hnorm : Continuous (fun st : I × I ↦ ‖gamma st.2‖) :=
      continuous_norm.comp hgamma
    have hquot : Continuous (fun st : I × I ↦ r / ‖gamma st.2‖) :=
      continuous_const.div hnorm
        (fun st ↦ norm_ne_zero_iff.mpr (hgamma0 st.2))
    have hscale : Continuous
        (fun st : I × I ↦ cartesianRadialScale r st.1 (gamma st.2)) := by
      dsimp [cartesianRadialScale]
      fun_prop
    exact (Complex.continuous_ofReal.comp hscale).mul hgamma
  map_zero_left t := by
    simp [banachRadialProjectionPath, cartesianRadialScale]
  map_one_left t := by
    simp [cartesianRadialScale]

/-- Exact Cauchy--Goursat identity on one explicit radial strip.  All
analytic input is discharged here.  A caller only has to prove the
elementary `C^2` regularity of its concrete affine or circular path.

The orientation is

`projected piece + terminal radial side = outer piece + initial radial side`.
-/
theorem banachRadialStripIdentity
    [CompleteSpace E]
    {F : ℂ → E} {eta m r : ℝ} {n : ℕ} {a b : ℂ}
    (gamma : Path a b)
    (hm : 0 ≤ m) (hr : 0 < r)
    (hgammaDelta : ∀ t, gamma t ∈ cartesianDelta eta m)
    (hrgamma : ∀ t, r ≤ ‖gamma t‖)
    (hF : DifferentiableOn ℂ F (cartesianDelta eta m))
    (hsmooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one
        ((banachRadialHomotopy gamma r
          (fun t ↦ norm_ne_zero_iff.mp
            (ne_of_gt (hr.trans_le (hrgamma t))))).extend xy.1) xy.2)
      (Icc 0 1)) :
    let hgamma0 : ∀ t, gamma t ≠ 0 := fun t ↦
      norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le (hrgamma t)))
    let phi := banachRadialHomotopy gamma r hgamma0
    let G := banachCoefficientIntegrand F n
    (∫ᶜ z in banachRadialProjectionPath gamma r hgamma0,
        banachHolomorphicOneForm G z) +
        (∫ᶜ z in phi.evalAt 1, banachHolomorphicOneForm G z) =
      (∫ᶜ z in gamma, banachHolomorphicOneForm G z) +
        (∫ᶜ z in phi.evalAt 0, banachHolomorphicOneForm G z) := by
  let hgamma0 : ∀ t, gamma t ≠ 0 := fun t ↦
    norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le (hrgamma t)))
  let phi := banachRadialHomotopy gamma r hgamma0
  let G := banachCoefficientIntegrand F n
  let U := cartesianDelta eta m \ {(0 : ℂ)}
  have hU : IsOpen U :=
    (isOpen_cartesianDelta eta m).sdiff isClosed_singleton
  have hphiU : Set.range phi ⊆ U := by
    rintro z ⟨st, rfl⟩
    have hs : (st.1 : ℝ) ∈ Icc (0 : ℝ) 1 := st.1.property
    have hmem := cartesianRadialHomotopy_mem hm hr
      (hrgamma st.2) hs (hgammaDelta st.2)
    refine ⟨hmem, ?_⟩
    simp only [mem_singleton_iff]
    exact mul_ne_zero
      (ofReal_ne_zero.mpr
        (cartesianRadialScale_pos_le_one hr (hrgamma st.2) hs).1.ne')
      (hgamma0 st.2)
  have hG : DifferentiableOn ℂ G U :=
    banachCoefficientIntegrand_differentiableOn hU
      (hF.mono sdiff_subset) (by simp [U])
  exact holomorphicCurveIntegral_boundary_eq_of_contDiffHomotopy
    phi hU hphiU hG hsmooth

omit [NormedSpace ℂ E] in
/-- Algebraic cancellation of the transverse radial sides for the six
pieces (five affine keyhole pieces and one major circular piece). -/
theorem six_radial_strips_telescope
    {p₀ p₁ p₂ p₃ p₄ p₅ o₀ o₁ o₂ o₃ o₄ o₅
      r₀ r₁ r₂ r₃ r₄ r₅ : E}
    (h₀ : p₀ + r₁ = o₀ + r₀)
    (h₁ : p₁ + r₂ = o₁ + r₁)
    (h₂ : p₂ + r₃ = o₂ + r₂)
    (h₃ : p₃ + r₄ = o₃ + r₃)
    (h₄ : p₄ + r₅ = o₄ + r₄)
    (h₅ : p₅ + r₀ = o₅ + r₅) :
    p₀ + p₁ + p₂ + p₃ + p₄ + p₅ =
      o₀ + o₁ + o₂ + o₃ + o₄ + o₅ := by
  have hp₀ : p₀ = o₀ + r₀ - r₁ := (eq_sub_iff_add_eq).2 h₀
  have hp₁ : p₁ = o₁ + r₁ - r₂ := (eq_sub_iff_add_eq).2 h₁
  have hp₂ : p₂ = o₂ + r₂ - r₃ := (eq_sub_iff_add_eq).2 h₂
  have hp₃ : p₃ = o₃ + r₃ - r₄ := (eq_sub_iff_add_eq).2 h₃
  have hp₄ : p₄ = o₄ + r₄ - r₅ := (eq_sub_iff_add_eq).2 h₄
  have hp₅ : p₅ = o₅ + r₅ - r₀ := (eq_sub_iff_add_eq).2 h₅
  rw [hp₀, hp₁, hp₂, hp₃, hp₄, hp₅]
  abel

/-- One-dimensional change of angular parameter, stated in exactly the
form used by the six radially projected pieces.  No monotonicity of the
angle lift is required, so the small backtracking along the rectangular
detour cancels automatically. -/
theorem intervalIntegral_angle_substitution
    [CompleteSpace E]
    {theta theta' : ℝ → ℝ} {H : ℝ → E} {a b : ℝ}
    (htheta : ∀ x ∈ [[a, b]], HasDerivAt theta (theta' x) x)
    (htheta' : ContinuousOn theta' [[a, b]])
    (hH : ContinuousOn H (theta '' [[a, b]])) :
    (∫ x in a..b, theta' x • H (theta x)) =
      ∫ u in theta a..theta b, H u := by
  simpa only [Function.comp_apply] using
    intervalIntegral.integral_deriv_smul_comp' htheta htheta' hH

/-- Telescoping five projected affine pieces only remembers the angle of
the two outer ray endpoints. -/
theorem five_angular_intervals_telescope
    [CompleteSpace E]
    {H : ℝ → E} (hH : Continuous H)
    (theta₀ theta₁ theta₂ theta₃ theta₄ theta₅ : ℝ) :
    (∫ x in theta₀..theta₁, H x) +
      (∫ x in theta₁..theta₂, H x) +
      (∫ x in theta₂..theta₃, H x) +
      (∫ x in theta₃..theta₄, H x) +
      (∫ x in theta₄..theta₅, H x) =
        ∫ x in theta₀..theta₅, H x := by
  rw [intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable theta₀ theta₁)
      (hH.intervalIntegrable theta₁ theta₂),
    intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable theta₀ theta₂)
      (hH.intervalIntegrable theta₂ theta₃),
    intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable theta₀ theta₃)
      (hH.intervalIntegrable theta₃ theta₄),
    intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable theta₀ theta₄)
      (hH.intervalIntegrable theta₄ theta₅)]

/-- Final orientation algebra.  The local projection runs from `theta₀`
to `-theta₀`; the fixed major arc runs from `2*pi-theta₀` back to
`theta₀`.  Their sum is the negative of one full positive circle. -/
theorem full_circle_add_local_and_major_angles_eq_zero
    [CompleteSpace E]
    {H : ℝ → E} (hH : Continuous H)
    (hperiod : Function.Periodic H (2 * Real.pi)) (theta₀ : ℝ) :
    (∫ x in 0..2 * Real.pi, H x) +
        (∫ x in theta₀..(-theta₀), H x) +
        (∫ x in (2 * Real.pi - theta₀)..theta₀, H x) = 0 := by
  have hadd :
      (∫ x in (-theta₀)..theta₀, H x) +
          (∫ x in theta₀..(2 * Real.pi - theta₀), H x) =
        ∫ x in (-theta₀)..(2 * Real.pi - theta₀), H x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable (-theta₀) theta₀)
      (hH.intervalIntegrable theta₀ (2 * Real.pi - theta₀))
  have hshift :
      (∫ x in (-theta₀)..(2 * Real.pi - theta₀), H x) =
        ∫ x in 0..2 * Real.pi, H x := by
    simpa only [zero_add, show -theta₀ + 2 * Real.pi =
        2 * Real.pi - theta₀ by ring] using
      hperiod.intervalIntegral_add_eq (-theta₀) 0
  have hsymLocal :
      (∫ x in theta₀..(-theta₀), H x) =
        -(∫ x in (-theta₀)..theta₀, H x) :=
    intervalIntegral.integral_symm (f := H) (μ := MeasureTheory.volume)
      (-theta₀) theta₀
  have hsymMajor :
      (∫ x in (2 * Real.pi - theta₀)..theta₀, H x) =
        -(∫ x in theta₀..(2 * Real.pi - theta₀), H x) :=
    intervalIntegral.integral_symm (f := H) (μ := MeasureTheory.volume) theta₀
      (2 * Real.pi - theta₀)
  rw [hsymLocal, hsymMajor]
  calc
    ((∫ x in 0..2 * Real.pi, H x) +
          -(∫ x in (-theta₀)..theta₀, H x)) +
        -(∫ x in theta₀..(2 * Real.pi - theta₀), H x) =
      (∫ x in 0..2 * Real.pi, H x) -
        ((∫ x in (-theta₀)..theta₀, H x) +
          ∫ x in theta₀..(2 * Real.pi - theta₀), H x) := by
            abel
    _ = (∫ x in 0..2 * Real.pi, H x) -
        (∫ x in (-theta₀)..(2 * Real.pi - theta₀), H x) := by
          rw [hadd]
    _ = 0 := by rw [hshift, sub_self]

/-! ### Orientation audit for the fixed outer circle -/

/-- The coefficient integrand pulled back to the endpoint circle. -/
def cartesianOuterCircleCoefficientIntegrand
    (F : ℂ → E) (M : ℝ) (n : ℕ) (theta : ℝ) : E :=
  let z := circleMap 0 (cartesianOuterRadius M) theta
  (deriv (circleMap 0 (cartesianOuterRadius M)) theta *
      z⁻¹ ^ (n + 1)) • F z

/-- The same major arc as `banachCartesianFixedOuterArcIntegral`, but in
the positive circle orientation, from the upper endpoint to the lower
endpoint. -/
def banachCartesianPositiveOuterMajorArcIntegral
    (F : ℂ → E) (M : ℝ) (n : ℕ) : E :=
  ∫ theta in cartesianOuterAngle M..
      (2 * Real.pi - cartesianOuterAngle M),
    cartesianOuterCircleCoefficientIntegrand F M n theta

theorem banachCartesianFixedOuterArcIntegral_eq_neg_positive
    (F : ℂ → E) (M : ℝ) (n : ℕ) :
    banachCartesianFixedOuterArcIntegral F M n =
      -banachCartesianPositiveOuterMajorArcIntegral F M n := by
  rfl

/-- The complementary minor arc in the positive circle orientation: from
the lower endpoint through angle `2*pi = 0` to the upper endpoint.  It is
introduced only to audit signs; it is not used for analytic estimates,
since it crosses the excluded cone. -/
def banachCartesianPositiveOuterMinorArcIntegral
    (F : ℂ → E) (M : ℝ) (n : ℕ) : E :=
  (∫ theta in (2 * Real.pi - cartesianOuterAngle M)..(2 * Real.pi),
      cartesianOuterCircleCoefficientIntegrand F M n theta) +
    ∫ theta in 0..cartesianOuterAngle M,
      cartesianOuterCircleCoefficientIntegrand F M n theta

/-- Splitting the endpoint circle at the two ray angles.  In particular,
`circle + fixedMajor = minor`, which is the algebraic sign check behind the
three-term global identity. -/
theorem circleIntegral_add_fixedOuterArc_eq_minor
    [CompleteSpace E]
    {F : ℂ → E} {M : ℝ} {n : ℕ}
    (hcont : Continuous
      (cartesianOuterCircleCoefficientIntegrand F M n)) :
    (∮ z in C((0 : ℂ), cartesianOuterRadius M),
        banachCoefficientIntegrand F n z) +
        banachCartesianFixedOuterArcIntegral F M n =
      banachCartesianPositiveOuterMinorArcIntegral F M n := by
  have h01 : IntervalIntegrable
      (cartesianOuterCircleCoefficientIntegrand F M n) volume
      0 (cartesianOuterAngle M) := hcont.intervalIntegrable _ _
  have h12 : IntervalIntegrable
      (cartesianOuterCircleCoefficientIntegrand F M n) volume
      (cartesianOuterAngle M)
      (2 * Real.pi - cartesianOuterAngle M) :=
    hcont.intervalIntegrable _ _
  have h23 : IntervalIntegrable
      (cartesianOuterCircleCoefficientIntegrand F M n) volume
      (2 * Real.pi - cartesianOuterAngle M) (2 * Real.pi) :=
    hcont.intervalIntegrable _ _
  have hcircle :
      (∮ z in C((0 : ℂ), cartesianOuterRadius M),
          banachCoefficientIntegrand F n z) =
        ∫ theta in 0..(2 * Real.pi),
          cartesianOuterCircleCoefficientIntegrand F M n theta := by
    rw [circleIntegral]
    apply intervalIntegral.integral_congr
    intro theta _
    simp only [cartesianOuterCircleCoefficientIntegrand,
      banachCoefficientIntegrand, smul_smul]
  have hfull :
      ((∫ theta in 0..cartesianOuterAngle M,
          cartesianOuterCircleCoefficientIntegrand F M n theta) +
        ∫ theta in cartesianOuterAngle M..
            (2 * Real.pi - cartesianOuterAngle M),
          cartesianOuterCircleCoefficientIntegrand F M n theta) +
        ∫ theta in (2 * Real.pi - cartesianOuterAngle M)..
            (2 * Real.pi),
          cartesianOuterCircleCoefficientIntegrand F M n theta =
        ∫ theta in 0..(2 * Real.pi),
          cartesianOuterCircleCoefficientIntegrand F M n theta := by
    rw [intervalIntegral.integral_add_adjacent_intervals h01 h12,
      intervalIntegral.integral_add_adjacent_intervals (h01.trans h12) h23]
  rw [hcircle, banachCartesianFixedOuterArcIntegral_eq_neg_positive,
    banachCartesianPositiveOuterMajorArcIntegral,
    banachCartesianPositiveOuterMinorArcIntegral, ← hfull]
  abel

/-! ### Smooth parametrized paths used by the six-piece radial deformation -/

/-- Restriction of a globally continuous real parametrization to the unit
interval, packaged as a `Path`. -/
def banachParamPath (gamma : ℝ → ℂ) (hgamma : Continuous gamma) :
    Path (gamma 0) (gamma 1) where
  toFun t := gamma t
  continuous_toFun := hgamma.comp continuous_subtype_val
  source' := by simp
  target' := by simp

@[simp]
theorem banachParamPath_apply
    (gamma : ℝ → ℂ) (hgamma : Continuous gamma) (t : I) :
    banachParamPath gamma hgamma t = gamma t := rfl

/-- Curve integration along a path obtained by restricting a globally
smooth parametrization.  This small bridge avoids any reparametrization
interface: it unfolds Mathlib's `derivWithin` definition on `Icc 0 1`. -/
theorem curveIntegral_banachParamPath
    [CompleteSpace E]
    {G : ℂ → E} {gamma gamma' : ℝ → ℂ}
    (hgamma : Continuous gamma)
    (hgamma' : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt gamma (gamma' t) t) :
    (∫ᶜ z in banachParamPath gamma hgamma,
        banachHolomorphicOneForm G z) =
      ∫ t in (0 : ℝ)..1, gamma' t • G (gamma t) := by
  rw [curveIntegral_def]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le zero_le_one]
  intro t ht
  rw [curveIntegralFun_def, Path.extend_apply _ ht,
    banachHolomorphicOneForm_apply]
  have hderiv : derivWithin gamma (Icc (0 : ℝ) 1) t = gamma' t :=
    (hgamma' t ht).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc zero_lt_one t ht)
  have hext : Set.EqOn (banachParamPath gamma hgamma).extend gamma
      (Icc (0 : ℝ) 1) := by
    intro x hx
    rw [Path.extend_apply _ hx]
    rfl
  rw [derivWithin_congr hext (hext ht), hderiv]
  rfl

/-- The circle path obtained from a real angle lift. -/
def banachAngularCirclePath
    (r : ℝ) (theta : ℝ → ℝ)
    (htheta : ContinuousOn theta (Icc (0 : ℝ) 1)) :
    Path (circleMap 0 r (theta 0)) (circleMap 0 r (theta 1)) where
  toFun t := circleMap 0 r (theta t)
  continuous_toFun :=
    ((continuous_circleMap 0 r).comp_continuousOn htheta).domRestrict
  source' := by simp
  target' := by simp

@[simp]
theorem banachAngularCirclePath_apply
    (r : ℝ) (theta : ℝ → ℝ)
    (htheta : ContinuousOn theta (Icc (0 : ℝ) 1)) (t : I) :
    banachAngularCirclePath r theta htheta t =
      circleMap 0 r (theta t) := by
  change circleMap 0 r (theta t) = circleMap 0 r (theta t)
  rfl

/-- Integral of an angular circle path, reduced exactly to an interval in
the angle variable. -/
theorem curveIntegral_banachAngularCirclePath
    [CompleteSpace E]
    {F : ℂ → E} {r : ℝ} {n : ℕ}
    {theta theta' : ℝ → ℝ}
    (htheta : ContinuousOn theta (Icc (0 : ℝ) 1))
    (hthetaDeriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt theta (theta' t) t)
    (htheta' : ContinuousOn theta' (Icc (0 : ℝ) 1))
    (hcircle : ContinuousOn (banachCircleCoefficientPullback F r n)
      (theta '' Icc (0 : ℝ) 1)) :
    (∫ᶜ z in banachAngularCirclePath r theta htheta,
        banachHolomorphicOneForm (banachCoefficientIntegrand F n) z) =
      ∫ u in theta 0..theta 1,
        banachCircleCoefficientPullback F r n u := by
  let gamma : ℝ → ℂ := fun t ↦ circleMap 0 r (theta t)
  let gamma' : ℝ → ℂ := fun t ↦
    theta' t • (circleMap 0 r (theta t) * Complex.I)
  have hgamma' : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt gamma (gamma' t) t := by
    intro t ht
    change HasDerivAt (circleMap 0 r ∘ theta)
      (theta' t • (circleMap 0 r (theta t) * Complex.I)) t
    exact (hasDerivAt_circleMap 0 r (theta t)).scomp t
      (hthetaDeriv t ht)
  rw [curveIntegral_def]
  have hcurve :
      (∫ t in (0 : ℝ)..1,
        curveIntegralFun
          (banachHolomorphicOneForm (banachCoefficientIntegrand F n))
          (banachAngularCirclePath r theta htheta) t) =
        ∫ t in (0 : ℝ)..1,
          gamma' t • banachCoefficientIntegrand F n (gamma t) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le zero_le_one]
    intro t ht
    rw [curveIntegralFun_def, Path.extend_apply _ ht,
      banachHolomorphicOneForm_apply]
    have hderiv : derivWithin gamma (Icc (0 : ℝ) 1) t = gamma' t :=
      (hgamma' t ht).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc zero_lt_one t ht)
    have hext : Set.EqOn
        (banachAngularCirclePath r theta htheta).extend gamma
        (Icc (0 : ℝ) 1) := by
      intro x hx
      rw [Path.extend_apply _ hx]
      simp [gamma]
    rw [derivWithin_congr hext (hext ht), hderiv]
    rfl
  rw [hcurve]
  have hintegrand (t : ℝ) :
      gamma' t • banachCoefficientIntegrand F n (gamma t) =
        theta' t • banachCircleCoefficientPullback F r n (theta t) := by
    dsimp [gamma, gamma', banachCoefficientIntegrand,
      banachCircleCoefficientPullback]
    rw [deriv_circleMap]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    apply congrArg (fun c : ℂ ↦ c • F (circleMap 0 r (theta t)))
    ac_rfl
  simp_rw [hintegrand]
  apply intervalIntegral_angle_substitution
  · simpa only [uIcc_of_le zero_le_one] using hthetaDeriv
  · simpa only [uIcc_of_le zero_le_one] using htheta'
  · simpa only [uIcc_of_le zero_le_one] using hcircle

/-- Linear radial homotopy from an angular circle path to a prescribed
parametrized path.  In applications the two endpoints are on the same
positive ray; keeping the formula linear makes its `C²` regularity
completely explicit. -/
def banachAngularRadialHomotopy
    (r : ℝ) (gamma : ℝ → ℂ) (theta : ℝ → ℝ)
    (hgamma : Continuous gamma)
    (htheta : ContinuousOn theta (Icc (0 : ℝ) 1)) :
    ((banachAngularCirclePath r theta htheta :
        Path (circleMap 0 r (theta 0)) (circleMap 0 r (theta 1))) :
      C(I, ℂ)).Homotopy
      (banachParamPath gamma hgamma : C(I, ℂ)) where
  toFun st :=
    (1 - (st.1 : ℝ)) • circleMap 0 r (theta st.2) +
      (st.1 : ℝ) • gamma st.2
  continuous_toFun := by
    have hthetaI : Continuous (fun t : I ↦ theta t) := htheta.domRestrict
    have hgammaI : Continuous (fun t : I ↦ gamma t) :=
      hgamma.comp continuous_subtype_val
    have hs : Continuous (fun st : I × I ↦ (st.1 : ℝ)) := by fun_prop
    have hcircle : Continuous
        (fun st : I × I ↦ circleMap 0 r (theta st.2)) := by
      exact (continuous_circleMap 0 r).comp
        (hthetaI.comp continuous_snd)
    exact (continuous_const.sub hs).smul hcircle |>.add
      (hs.smul (hgammaI.comp continuous_snd))
  map_zero_left t := by
    simp [banachAngularCirclePath_apply]
  map_one_left t := by
    simp [banachParamPath]

/-- On the closed unit square, the doubly extended angular radial
homotopy agrees with its globally smooth defining formula. -/
theorem banachAngularRadialHomotopy_contDiffOn
    {r : ℝ} {gamma : ℝ → ℂ} {theta : ℝ → ℝ}
    (hgamma : ContDiff ℝ 2 gamma)
    (htheta : ContDiffOn ℝ 2 theta (Icc (0 : ℝ) 1)) :
    let cgamma := hgamma.continuous
    let ctheta := htheta.continuousOn
    let phi := banachAngularRadialHomotopy r gamma theta cgamma ctheta
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one
        (phi.extend xy.1) xy.2) (Icc 0 1) := by
  let cgamma := hgamma.continuous
  let ctheta := htheta.continuousOn
  let phi := banachAngularRadialHomotopy r gamma theta cgamma ctheta
  let psi : ℝ × ℝ → ℂ := fun xy ↦
    (1 - xy.1) • circleMap 0 r (theta xy.2) +
      xy.1 • gamma xy.2
  have hsndTheta : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ ↦ theta xy.2)
      (Icc 0 1) :=
    htheta.comp contDiffOn_snd (by
      intro xy hxy
      exact ⟨hxy.1.2, hxy.2.2⟩)
  have hsndGamma : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ ↦ gamma xy.2)
      (Icc 0 1) :=
    hgamma.contDiffOn.comp contDiffOn_snd (by
      intro xy hxy
      exact Set.mem_univ _)
  have hcircle : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ circleMap 0 r (theta xy.2)) (Icc 0 1) :=
    (contDiff_circleMap 0 r).comp_contDiffOn hsndTheta
  have hfst : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ ↦ xy.1) (Icc 0 1) :=
    contDiffOn_fst
  have hpsi : ContDiffOn ℝ 2 psi (Icc 0 1) := by
    exact (contDiffOn_const.sub hfst).smul hcircle |>.add
      (hfst.smul hsndGamma)
  apply hpsi.congr
  intro xy hxy
  have hs : xy.1 ∈ Icc (0 : ℝ) 1 := ⟨hxy.1.1, hxy.2.1⟩
  have ht : xy.2 ∈ Icc (0 : ℝ) 1 := ⟨hxy.1.2, hxy.2.2⟩
  rw [Set.IccExtend_of_mem zero_le_one _ ht,
    phi.extend_apply_of_mem_I hs]
  rfl

/-- Common value of an oriented radial side, expressed with the affine
base convention already used by the local keyhole. -/
def banachRadialSideIntegral
    (G : ℂ → E) (r : ℝ) (z : ℂ) : E :=
  let p := ((r / ‖z‖ : ℝ) : ℂ) * z
  banachAffineBaseIntegral G p (z - p) 0 1

set_option backward.isDefEq.respectTransparency.types false in
/-- The endpoint path of the angular radial homotopy has exactly the
common radial-side integral. -/
theorem curveIntegral_banachAngularRadialHomotopy_evalAt
    [CompleteSpace E]
    {G : ℂ → E} {r : ℝ}
    {gamma : ℝ → ℂ} {theta : ℝ → ℝ}
    (hgamma : Continuous gamma)
    (htheta : ContinuousOn theta (Icc (0 : ℝ) 1))
    {t : I}
    (hproj : circleMap 0 r (theta t) =
      ((r / ‖gamma t‖ : ℝ) : ℂ) * gamma t) :
    let phi := banachAngularRadialHomotopy r gamma theta hgamma htheta
    (∫ᶜ z in phi.evalAt t,
        banachHolomorphicOneForm G z) =
      banachRadialSideIntegral G r (gamma t) := by
  dsimp only
  let phi := banachAngularRadialHomotopy r gamma theta hgamma htheta
  let c := circleMap 0 r (theta t)
  let z := gamma t
  let side : ℝ → ℂ := fun s ↦ c + s • (z - c)
  change (∫ᶜ w in phi.evalAt t,
      banachHolomorphicOneForm G w) =
    banachRadialSideIntegral G r (gamma t)
  rw [curveIntegral_def]
  dsimp [banachRadialSideIntegral, banachAffineBaseIntegral]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le zero_le_one]
  intro s hs
  rw [curveIntegralFun_def, banachHolomorphicOneForm_apply]
  have hsideDeriv : HasDerivAt side (z - c) s := by
    simpa [side] using
      ((hasDerivAt_id' s).smul_const (z - c)).const_add c
  have hext : Set.EqOn (phi.evalAt t).extend side
      (Icc (0 : ℝ) 1) := by
    intro u hu
    rw [Path.extend_apply _ hu]
    change (1 - (u : ℝ)) • circleMap 0 r (theta t) +
      (u : ℝ) • gamma t = side u
    dsimp [side, c, z]
    simp
    ring
  calc
    _ = derivWithin side (Icc (0 : ℝ) 1) s • G (side s) := by
      exact congrArg₂ (fun (v w : ℂ) ↦ v • G w)
        (derivWithin_congr hext (hext hs)) (hext hs)
    _ = _ := by
      rw [hsideDeriv.hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc zero_lt_one s hs)]
      dsimp [side, c, z]
      rw [hproj]
      simp
      ring_nf

/-- Exact strip identity already translated to an angular interval and
the common radial-side convention.  All hypotheses are elementary
properties of the concrete affine or circular parametrization. -/
theorem banachParametricAngularStripIdentity
    [CompleteSpace E]
    {F : ℂ → E} {eta m r : ℝ} {n : ℕ}
    {gamma : ℝ → ℂ} {theta theta' : ℝ → ℝ}
    (hm : 0 ≤ m) (hr : 0 < r)
    (hgamma : ContDiff ℝ 2 gamma)
    (htheta : ContDiffOn ℝ 2 theta (Icc (0 : ℝ) 1))
    (hthetaDeriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt theta (theta' t) t)
    (htheta' : ContinuousOn theta' (Icc (0 : ℝ) 1))
    (hproj : ∀ t ∈ Icc (0 : ℝ) 1,
      circleMap 0 r (theta t) =
        ((r / ‖gamma t‖ : ℝ) : ℂ) * gamma t)
    (hgammaDelta : ∀ t ∈ Icc (0 : ℝ) 1,
      gamma t ∈ cartesianDelta eta m)
    (hrgamma : ∀ t ∈ Icc (0 : ℝ) 1, r ≤ ‖gamma t‖)
    (hcircle : ContinuousOn (banachCircleCoefficientPullback F r n)
      (theta '' Icc (0 : ℝ) 1))
    (hF : DifferentiableOn ℂ F (cartesianDelta eta m)) :
    let G := banachCoefficientIntegrand F n
    (∫ u in theta 0..theta 1,
        banachCircleCoefficientPullback F r n u) +
        banachRadialSideIntegral G r (gamma 1) =
      (∫ᶜ z in banachParamPath gamma hgamma.continuous,
        banachHolomorphicOneForm G z) +
        banachRadialSideIntegral G r (gamma 0) := by
  let cgamma := hgamma.continuous
  let ctheta := htheta.continuousOn
  let phi := banachAngularRadialHomotopy r gamma theta cgamma ctheta
  let G := banachCoefficientIntegrand F n
  let U := cartesianDelta eta m \ {(0 : ℂ)}
  have hU : IsOpen U :=
    (isOpen_cartesianDelta eta m).sdiff isClosed_singleton
  have hphiU : Set.range phi ⊆ U := by
    rintro z ⟨st, rfl⟩
    have hs : (st.1 : ℝ) ∈ Icc (0 : ℝ) 1 := st.1.property
    have ht : (st.2 : ℝ) ∈ Icc (0 : ℝ) 1 := st.2.property
    have hmem := cartesianRadialHomotopy_mem hm hr
      (hrgamma st.2 ht) hs (hgammaDelta st.2 ht)
    have heq : phi st =
        ((cartesianRadialScale r st.1 (gamma st.2) : ℝ) : ℂ) *
          gamma st.2 := by
      change (1 - (st.1 : ℝ)) •
          circleMap 0 r (theta st.2) +
          (st.1 : ℝ) • gamma st.2 = _
      rw [hproj st.2 ht]
      apply Complex.ext <;>
        simp [cartesianRadialScale, Algebra.smul_def,
          Complex.mul_re, Complex.mul_im] <;>
        ring
    rw [heq]
    refine ⟨hmem, ?_⟩
    simp only [mem_singleton_iff]
    exact mul_ne_zero
      (ofReal_ne_zero.mpr
        (cartesianRadialScale_pos_le_one hr (hrgamma st.2 ht) hs).1.ne')
      (norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le (hrgamma st.2 ht))))
  have hG : DifferentiableOn ℂ G U :=
    banachCoefficientIntegrand_differentiableOn hU
      (hF.mono sdiff_subset) (by simp [U])
  have hid := holomorphicCurveIntegral_boundary_eq_of_contDiffHomotopy
    phi hU hphiU hG
      (banachAngularRadialHomotopy_contDiffOn hgamma htheta)
  dsimp only [phi, G] at hid
  rw [curveIntegral_banachAngularCirclePath ctheta hthetaDeriv
      htheta' hcircle,
    curveIntegral_banachAngularRadialHomotopy_evalAt
      cgamma ctheta (t := (1 : I)) (hproj 1 (by simp)),
    curveIntegral_banachAngularRadialHomotopy_evalAt
      cgamma ctheta (t := (0 : I)) (hproj 0 (by simp))] at hid
  exact hid

/-- One of the five affine keyhole pieces, radially projected to the common
inner circle.  Positivity of the real part provides the elementary angle
lift; all smoothness and substitution facts are discharged internally. -/
theorem banachAffineAngularStripIdentity
    [CompleteSpace E]
    {F : ℂ → E} {eta m r : ℝ} {n : ℕ}
    (p q : ℂ) (a b : ℝ)
    (hm : 0 ≤ m) (hr : 0 < r)
    (hdelta : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap (p + q * (a : ℂ)) (p + q * (b : ℂ)) t ∈
        cartesianDelta eta m)
    (hrnorm : ∀ t ∈ Icc (0 : ℝ) 1, r ≤
      ‖AffineMap.lineMap (p + q * (a : ℂ))
        (p + q * (b : ℂ)) t‖)
    (hre : ∀ t ∈ Icc (0 : ℝ) 1, 0 <
      (AffineMap.lineMap (p + q * (a : ℂ))
        (p + q * (b : ℂ)) t).re)
    (hcircle : Continuous
      (banachCircleCoefficientPullback F r n))
    (hF : DifferentiableOn ℂ F (cartesianDelta eta m)) :
    let G := banachCoefficientIntegrand F n
    let A := p + q * (a : ℂ)
    let B := p + q * (b : ℂ)
    (∫ u in cartesianRightHalfAngle A..cartesianRightHalfAngle B,
        banachCircleCoefficientPullback F r n u) +
        banachRadialSideIntegral G r B =
      banachAffineBaseIntegral G p q a b +
        banachRadialSideIntegral G r A := by
  let A := p + q * (a : ℂ)
  let B := p + q * (b : ℂ)
  let gamma : ℝ → ℂ := AffineMap.lineMap A B
  let theta : ℝ → ℝ := fun t ↦ cartesianRightHalfAngle (gamma t)
  let theta' : ℝ → ℝ := fun t ↦ deriv theta t
  let V : Set ℝ := {t | 0 < (gamma t).re}
  have hgamma : ContDiff ℝ 2 gamma := by
    change ContDiff ℝ 2 (fun t : ℝ ↦ t • (B - A) + A)
    fun_prop
  have hVopen : IsOpen V := by
    dsimp [V]
    exact isOpen_lt continuous_const
      (Complex.continuous_re.comp hgamma.continuous)
  have hIccV : Icc (0 : ℝ) 1 ⊆ V := by
    intro t ht
    exact hre t ht
  have hthetaV : ContDiffOn ℝ 2 theta V := by
    intro t ht
    have hgt : (gamma t).re ≠ 0 := ne_of_gt ht
    exact (contDiffAt_cartesianRightHalfAngle hgt).comp t
      hgamma.contDiffAt |>.contDiffWithinAt
  have htheta : ContDiffOn ℝ 2 theta (Icc (0 : ℝ) 1) :=
    hthetaV.mono hIccV
  have hthetaDeriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt theta (theta' t) t := by
    intro t ht
    have hthetaAt : ContDiffAt ℝ 2 theta t :=
      (hthetaV t (hIccV ht)).contDiffAt
        (hVopen.mem_nhds (hIccV ht))
    exact (hthetaAt.differentiableAt (by norm_num)).hasDerivAt
  have htheta' : ContinuousOn theta' (Icc (0 : ℝ) 1) := by
    have hderivV : ContDiffOn ℝ 1 (deriv theta) V :=
      hthetaV.deriv_of_isOpen hVopen (by norm_num)
    exact hderivV.continuousOn.mono hIccV
  have hproj : ∀ t ∈ Icc (0 : ℝ) 1,
      circleMap 0 r (theta t) =
        ((r / ‖gamma t‖ : ℝ) : ℂ) * gamma t := by
    intro t ht
    exact circleMap_cartesianRightHalfAngle (hre t ht)
  have hid := banachParametricAngularStripIdentity
    (F := F) (eta := eta) (m := m) (r := r) (n := n)
    hm hr hgamma htheta hthetaDeriv htheta' hproj hdelta hrnorm
    hcircle.continuousOn hF
  have houter :
      (∫ᶜ z in banachParamPath gamma hgamma.continuous,
        banachHolomorphicOneForm
          (banachCoefficientIntegrand F n) z) =
        banachAffineBaseIntegral
          (banachCoefficientIntegrand F n) p q a b := by
    calc
      (∫ᶜ z in banachParamPath gamma hgamma.continuous,
          banachHolomorphicOneForm
            (banachCoefficientIntegrand F n) z) =
          (∫ᶜ z in Path.segment A B,
            banachHolomorphicOneForm
              (banachCoefficientIntegrand F n) z) := by
            rw [curveIntegral_banachParamPath
              (G := banachCoefficientIntegrand F n)
              (gamma' := fun _ ↦ B - A) hgamma.continuous]
            · rw [curveIntegral_segment]
              apply intervalIntegral.integral_congr
              intro t _
              simp [gamma, banachHolomorphicOneForm_apply]
            · intro t _
              exact AffineMap.hasDerivAt_lineMap
      _ = banachAffineBaseIntegral
          (banachCoefficientIntegrand F n) p q a b := by
            simpa [A, B, banachAffinePath] using
              (curveIntegral_banachAffinePath
                (G := banachCoefficientIntegrand F n) p q a b)
  dsimp only at hid ⊢
  rw [houter] at hid
  simpa [theta, gamma, A, B] using hid

/-- The fixed major outer arc, with its actual lower-to-upper orientation,
radially projected to the same inner circle. -/
theorem banachOuterMajorAngularStripIdentity
    [CompleteSpace E]
    {F : ℂ → E} {eta m r M : ℝ} {n : ℕ}
    (hM : 0 < M) (hMeta : M < eta)
    (hm0 : 0 ≤ m) (hm43 : m < 4 / 3)
    (hr : 0 < r) (hrR : r ≤ cartesianOuterRadius M)
    (hcircle : Continuous (banachCircleCoefficientPullback F r n))
    (hF : DifferentiableOn ℂ F (cartesianDelta eta m)) :
    let G := banachCoefficientIntegrand F n
    let A := (1 : ℂ) + cartesianUpperDir * (M : ℂ)
    let B := (1 : ℂ) + cartesianLowerDir * (M : ℂ)
    (∫ u in (2 * Real.pi - cartesianOuterAngle M)..
        cartesianOuterAngle M,
        banachCircleCoefficientPullback F r n u) +
        banachRadialSideIntegral G r A =
      banachCartesianFixedOuterArcIntegral F M n +
        banachRadialSideIntegral G r B := by
  let alpha := cartesianOuterAngle M
  let R := cartesianOuterRadius M
  let A := (1 : ℂ) + cartesianUpperDir * (M : ℂ)
  let B := (1 : ℂ) + cartesianLowerDir * (M : ℂ)
  let theta : ℝ → ℝ := fun t ↦
    (2 * Real.pi - alpha) + (2 * alpha - 2 * Real.pi) * t
  let theta' : ℝ → ℝ := fun _ ↦ 2 * alpha - 2 * Real.pi
  let gamma : ℝ → ℂ := fun t ↦ circleMap 0 R (theta t)
  have htheta : ContDiff ℝ 2 theta := by
    dsimp [theta]
    fun_prop
  have hthetaDeriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt theta (theta' t) t := by
    intro t _
    change HasDerivAt
      (fun x : ℝ ↦ (2 * Real.pi - alpha) +
        (2 * alpha - 2 * Real.pi) * x)
      (2 * alpha - 2 * Real.pi) t
    simpa only [id_eq, one_mul, mul_one] using
      ((hasDerivAt_id t).const_mul
        (2 * alpha - 2 * Real.pi)).const_add
          (2 * Real.pi - alpha)
  have htheta' : ContinuousOn theta' (Icc (0 : ℝ) 1) := by
    dsimp [theta']
    fun_prop
  have hgamma : ContDiff ℝ 2 gamma := by
    dsimp [gamma]
    exact (contDiff_circleMap 0 R).comp htheta
  have hthetaRange : ∀ t ∈ Icc (0 : ℝ) 1,
      theta t ∈ Icc alpha (2 * Real.pi - alpha) := by
    intro t ht
    have halpha := cartesianOuterAngle_interval_nonempty M
    have hgap : 0 ≤ 2 * Real.pi - 2 * alpha := by
      linarith
    dsimp [theta]
    constructor
    · nlinarith [mul_nonneg hgap (sub_nonneg.mpr ht.2)]
    · nlinarith [mul_nonneg hgap ht.1]
  have hgammaDelta : ∀ t ∈ Icc (0 : ℝ) 1,
      gamma t ∈ cartesianDelta eta m := by
    intro t ht
    exact cartesianOuterMajorArc_subset_cartesianDelta hM hMeta hm43
      (cartesianOuterCircleMap_mem_majorArc hM (hthetaRange t ht))
  have hgammaNorm : ∀ t ∈ Icc (0 : ℝ) 1, r ≤ ‖gamma t‖ := by
    intro t _
    dsimp [gamma, R]
    rw [cartesianOuterCircleMap_constant_norm hM]
    exact hrR
  have hproj : ∀ t ∈ Icc (0 : ℝ) 1,
      circleMap 0 r (theta t) =
        ((r / ‖gamma t‖ : ℝ) : ℂ) * gamma t := by
    intro t _
    have hRpos : 0 < R :=
      lt_trans zero_lt_one (cartesianOuterRadius_gt_one hM)
    dsimp [gamma]
    rw [cartesianOuterCircleMap_constant_norm hM]
    simp only [circleMap_zero]
    calc
      (r : ℂ) * Complex.exp ((theta t : ℂ) * Complex.I) =
          (((r / R : ℝ) : ℂ) * (R : ℂ)) *
            Complex.exp ((theta t : ℂ) * Complex.I) := by
              congr 2
              rw [← ofReal_mul, div_mul_cancel₀ r hRpos.ne']
      _ = ((r / R : ℝ) : ℂ) *
          ((R : ℂ) * Complex.exp
            ((theta t : ℂ) * Complex.I)) := by ring
  have hcircleOuter : ContinuousOn
      (banachCircleCoefficientPullback F R n)
      (theta '' Icc (0 : ℝ) 1) := by
    intro u hu
    rcases hu with ⟨t, ht, rfl⟩
    let z := circleMap 0 R (theta t)
    have hzMajor : z ∈ cartesianOuterMajorArc M := by
      exact cartesianOuterCircleMap_mem_majorArc hM (hthetaRange t ht)
    have hzDelta : z ∈ cartesianDelta eta m :=
      cartesianOuterMajorArc_subset_cartesianDelta hM hMeta hm43 hzMajor
    have hFdiff : DifferentiableAt ℂ F z :=
      (hF z hzDelta).differentiableAt
        ((isOpen_cartesianDelta eta m).mem_nhds hzDelta)
    have hFcont : ContinuousAt F z := hFdiff.continuousAt
    have hzcont : ContinuousAt (fun u : ℝ ↦ circleMap 0 R u) (theta t) :=
      (continuous_circleMap 0 R).continuousAt
    have hz0 : z ≠ 0 := by
      apply norm_ne_zero_iff.mp
      dsimp [z, R]
      rw [cartesianOuterCircleMap_constant_norm hM]
      exact (lt_trans zero_lt_one (cartesianOuterRadius_gt_one hM)).ne'
    have hdercont : ContinuousAt
        (fun u : ℝ ↦ deriv (circleMap 0 R) u) (theta t) := by
      simp only [deriv_circleMap]
      fun_prop
    exact (hdercont.mul ((hzcont.inv₀ hz0).pow (n + 1))).smul
      (hFcont.comp_of_eq hzcont rfl) |>.continuousWithinAt
  have hid := banachParametricAngularStripIdentity
    (F := F) (eta := eta) (m := m) (r := r) (n := n)
    hm0 hr hgamma htheta.contDiffOn hthetaDeriv htheta'
    hproj hgammaDelta hgammaNorm
    hcircle.continuousOn hF
  have htarget :
      (∫ᶜ z in banachParamPath gamma hgamma.continuous,
        banachHolomorphicOneForm (banachCoefficientIntegrand F n) z) =
        banachCartesianFixedOuterArcIntegral F M n := by
    rw [curveIntegral_banachParamPath
      (G := banachCoefficientIntegrand F n)
      (gamma' := fun t ↦
        theta' t • (circleMap 0 R (theta t) * Complex.I))
      hgamma.continuous]
    · have hintegrand (t : ℝ) :
          (theta' t • (circleMap 0 R (theta t) * Complex.I)) •
              banachCoefficientIntegrand F n (circleMap 0 R (theta t)) =
            theta' t •
              banachCircleCoefficientPullback F R n (theta t) := by
          dsimp [banachCoefficientIntegrand,
            banachCircleCoefficientPullback]
          rw [deriv_circleMap]
          simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
          apply congrArg
            (fun c : ℂ ↦ c • F (circleMap 0 R (theta t)))
          ac_rfl
      simp only [gamma]
      simp_rw [hintegrand]
      rw [intervalIntegral_angle_substitution]
      · rw [show theta 0 = 2 * Real.pi - alpha by
            simp [theta],
          show theta 1 = alpha by
            dsimp [theta]
            ring,
          intervalIntegral.integral_symm]
        change -( ∫ x in alpha..2 * Real.pi - alpha,
          banachCircleCoefficientPullback F R n x) = _
        rfl
      · simpa only [uIcc_of_le zero_le_one] using hthetaDeriv
      · simpa only [uIcc_of_le zero_le_one] using htheta'
      · simpa only [uIcc_of_le zero_le_one] using hcircleOuter
    · intro t ht
      change HasDerivAt (circleMap 0 R ∘ theta)
        (theta' t • (circleMap 0 R (theta t) * Complex.I)) t
      exact (hasDerivAt_circleMap 0 R (theta t)).scomp t
        (hthetaDeriv t ht)
  dsimp only at hid ⊢
  rw [htarget] at hid
  have htheta0 : theta 0 = 2 * Real.pi - cartesianOuterAngle M := by
    simp [theta, alpha]
  have htheta1 : theta 1 = cartesianOuterAngle M := by
    simp [theta, alpha]
    ring
  have hgamma0 : gamma 0 = B := by
    dsimp [gamma, theta, alpha, R, B]
    convert cartesianOuterCircleMap_at_two_pi_sub_angle M using 2
    all_goals ring
  have hgamma1 : gamma 1 = A := by
    dsimp [gamma, theta, alpha, R, A]
    convert cartesianOuterCircleMap_at_angle M using 2
    all_goals ring
  simpa [htheta0, htheta1, hgamma0, hgamma1, A, B] using hid

omit [NormedSpace ℂ E] in
/-- A real affine parameter between `0` and `1` stays in the unoriented
interval determined by its endpoints. -/
theorem real_lineMap_mem_uIcc (a b t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap a b t ∈ [[a, b]] := by
  rw [← segment_eq_uIcc]
  exact lineMap_mem_segment ℝ a b ht

omit [NormedSpace ℂ E] in
/-- Complex affine interpolation agrees with interpolation of the real
parameter in an affine complex line. -/
theorem complex_affine_lineMap_eq
    (p q : ℂ) (a b t : ℝ) :
    AffineMap.lineMap (p + q * (a : ℂ)) (p + q * (b : ℂ)) t =
      p + q * (AffineMap.lineMap a b t : ℝ) := by
  apply Complex.ext <;>
    simp [AffineMap.lineMap_apply, Complex.mul_re, Complex.mul_im] <;>
    ring

omit [NormedSpace ℂ E] in
/-- A lower bound on the real parts of two endpoints propagates along the
whole affine segment. -/
theorem lineMap_re_lower_bound
    {A B : ℂ} {c t : ℝ}
    (hA : c ≤ A.re) (hB : c ≤ B.re)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    c ≤ (AffineMap.lineMap A B t).re := by
  calc
    c = (1 - t) * c + t * c := by ring
    _ ≤ (1 - t) * A.re + t * B.re :=
      add_le_add
        (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hB ht.1)
    _ = (AffineMap.lineMap A B t).re := by
      rw [AffineMap.lineMap_apply_module]
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]

/-- Exact global Cartesian contour closure.  It is obtained by six
explicit smooth radial strips (the five affine keyhole pieces and the
fixed major arc), so no contour-deformation principle appears among the
hypotheses. -/
theorem banachCartesianGlobalContourIdentity
    [CompleteSpace E]
    {F : ℂ → E} {M eta m : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hrhoM : cartesianDetourRadius n ≤ M)
    (hMeta : M < eta) (heta : 1 / (n : ℝ) < eta)
    (hm0 : 0 ≤ m) (hm43 : m < 4 / 3)
    (hF : DifferentiableOn ℂ F (cartesianDelta eta m)) :
    (∮ z in C((0 : ℂ), (1 / 2 : ℝ)),
        banachCoefficientIntegrand F n z) +
        banachCartesianLocalKeyhole F M n +
        banachCartesianFixedOuterArcIntegral F M n = 0 := by
  let rho := cartesianDetourRadius n
  let r : ℝ := 1 / 2
  let G := banachCoefficientIntegrand F n
  let H := banachCircleCoefficientPullback F r n
  let z₀ : ℂ := 1 + cartesianUpperDir * (M : ℂ)
  let z₁ : ℂ := 1 + cartesianUpperDir * (rho : ℂ)
  let z₂ : ℂ :=
    1 - (rho : ℂ) + (4 * rho / 5 : ℝ) * Complex.I
  let z₃ : ℂ :=
    1 - (rho : ℂ) - (4 * rho / 5 : ℝ) * Complex.I
  let z₄ : ℂ := 1 + cartesianLowerDir * (rho : ℂ)
  let z₅ : ℂ := 1 + cartesianLowerDir * (M : ℂ)
  have hrho : 0 < rho := by
    dsimp [rho, cartesianDetourRadius]
    positivity
  have hrhoHalf : rho < r := by
    have hnR : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
    dsimp [rho, r, cartesianDetourRadius]
    have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * n)]
    nlinarith
  have hr : 0 < r := by norm_num [r]
  have hM : 0 < M := hrho.trans_le hrhoM
  obtain ⟨hupper, htop, hleft, hbottom, hlower⟩ :=
    banachCartesianLocalKeyhole_segments_mem
      hn hrhoM hMeta heta hm43
  have hInnerDelta : ∀ u : ℝ,
      circleMap 0 r u ∈ cartesianDelta eta m := by
    intro u
    constructor
    · rw [norm_circleMap_zero, abs_of_pos hr]
      dsimp [r]
      linarith
    · intro hcone
      have hreNorm := (le_abs_self (circleMap 0 r u).re).trans
        (Complex.abs_re_le_norm (circleMap 0 r u))
      have hnorm : ‖circleMap 0 r u‖ = r := by
        rw [norm_circleMap_zero, abs_of_pos hr]
      have hreOne : 1 ≤ (circleMap 0 r u).re := by
        simpa only [Complex.sub_re, Complex.one_re, sub_nonneg] using hcone.1
      rw [hnorm] at hreNorm
      dsimp [r] at hreNorm
      linarith
  have hH : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro u
    let z := circleMap 0 r u
    have hzDelta : z ∈ cartesianDelta eta m := hInnerDelta u
    have hFdiff : DifferentiableAt ℂ F z :=
      (hF z hzDelta).differentiableAt
        ((isOpen_cartesianDelta eta m).mem_nhds hzDelta)
    have hFcont : ContinuousAt F z := hFdiff.continuousAt
    have hzcont : ContinuousAt (fun v : ℝ ↦ circleMap 0 r v) u :=
      (continuous_circleMap 0 r).continuousAt
    have hz0 : z ≠ 0 := by
      apply norm_ne_zero_iff.mp
      dsimp [z]
      rw [norm_circleMap_zero, abs_of_pos hr]
      exact hr.ne'
    have hdercont : ContinuousAt
        (fun v : ℝ ↦ deriv (circleMap 0 r) v) u := by
      simp only [deriv_circleMap]
      fun_prop
    dsimp [H, banachCircleCoefficientPullback]
    exact (hdercont.mul ((hzcont.inv₀ hz0).pow (n + 1))).smul
      (hFcont.comp_of_eq hzcont rfl)
  have hAffineBounds : ∀ (A B : ℂ), r ≤ A.re → r ≤ B.re →
      (∀ t ∈ Icc (0 : ℝ) 1,
        r ≤ ‖AffineMap.lineMap A B t‖) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        0 < (AffineMap.lineMap A B t).re) := by
    intro A B hA hB
    constructor
    · intro t ht
      have hreal := lineMap_re_lower_bound hA hB ht
      exact hreal.trans ((le_abs_self _).trans
        (Complex.abs_re_le_norm (AffineMap.lineMap A B t)))
    · intro t ht
      exact hr.trans_le (lineMap_re_lower_bound hA hB ht)
  have hz₀re : r ≤ z₀.re := by
    dsimp [z₀, r]
    simp [cartesianUpperDir]
    linarith
  have hz₁re : r ≤ z₁.re := by
    dsimp [z₁, r]
    simp [cartesianUpperDir]
    linarith
  have hz₂re : r ≤ z₂.re := by
    dsimp [z₂, r]
    simp
    have hrhoHalf' := hrhoHalf
    dsimp [r] at hrhoHalf'
    linarith
  have hz₃re : r ≤ z₃.re := by
    dsimp [z₃, r]
    simp
    have hrhoHalf' := hrhoHalf
    dsimp [r] at hrhoHalf'
    linarith
  have hz₄re : r ≤ z₄.re := by
    dsimp [z₄, r]
    simp [cartesianLowerDir]
    linarith
  have hz₅re : r ≤ z₅.re := by
    dsimp [z₅, r]
    simp [cartesianLowerDir]
    linarith
  obtain ⟨hnorm₀, hre₀⟩ := hAffineBounds z₀ z₁ hz₀re hz₁re
  obtain ⟨hnorm₁, hre₁⟩ := hAffineBounds z₁ z₂ hz₁re hz₂re
  obtain ⟨hnorm₂, hre₂⟩ := hAffineBounds z₂ z₃ hz₂re hz₃re
  obtain ⟨hnorm₃, hre₃⟩ := hAffineBounds z₃ z₄ hz₃re hz₄re
  obtain ⟨hnorm₄, hre₄⟩ := hAffineBounds z₄ z₅ hz₄re hz₅re
  have hz₁top : z₁ =
      (1 + (4 * rho / 5 : ℝ) * Complex.I) +
        (1 : ℂ) * ((3 * rho / 5 : ℝ) : ℂ) := by
    dsimp [z₁]
    apply Complex.ext <;> simp [cartesianUpperDir] <;> ring
  have hz₂top : z₂ =
      (1 + (4 * rho / 5 : ℝ) * Complex.I) +
        (1 : ℂ) * ((-rho : ℝ) : ℂ) := by
    dsimp [z₂]
    apply Complex.ext
    · norm_num
      ring
    · norm_num
  have hz₂left : z₂ =
      (1 - (rho : ℂ)) +
        Complex.I * ((4 * rho / 5 : ℝ) : ℂ) := by
    dsimp [z₂]
    apply Complex.ext <;> simp
  have hz₃left : z₃ =
      (1 - (rho : ℂ)) +
        Complex.I * ((-(4 * rho / 5) : ℝ) : ℂ) := by
    dsimp [z₃]
    apply Complex.ext <;> simp
  have hz₃bottom : z₃ =
      (1 - (4 * rho / 5 : ℝ) * Complex.I) +
        (1 : ℂ) * ((-rho : ℝ) : ℂ) := by
    dsimp [z₃]
    apply Complex.ext
    · norm_num
      ring
    · norm_num
  have hz₄bottom : z₄ =
      (1 - (4 * rho / 5 : ℝ) * Complex.I) +
        (1 : ℂ) * ((3 * rho / 5 : ℝ) : ℂ) := by
    dsimp [z₄]
    apply Complex.ext <;> simp [cartesianLowerDir] <;> ring
  have hdelta₀ : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap z₀ z₁ t ∈ cartesianDelta eta m := by
    intro t ht
    let x := AffineMap.lineMap M rho t
    have hx : x ∈ [[M, rho]] := real_lineMap_mem_uIcc M rho t ht
    have hmemb := (hupper x hx).1
    rw [show AffineMap.lineMap z₀ z₁ t =
        1 + cartesianUpperDir * (x : ℂ) by
      dsimp [z₀, z₁, x]
      simpa using complex_affine_lineMap_eq
        (1 : ℂ) cartesianUpperDir M rho t]
    exact hmemb
  have hdelta₁ : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap z₁ z₂ t ∈ cartesianDelta eta m := by
    intro t ht
    let x := AffineMap.lineMap (3 * rho / 5) (-rho) t
    have hx : x ∈ [[3 * rho / 5, -rho]] :=
      real_lineMap_mem_uIcc _ _ t ht
    have hmemb := (htop x hx).1
    rw [hz₁top, hz₂top, complex_affine_lineMap_eq]
    simpa [x] using hmemb
  have hdelta₂ : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap z₂ z₃ t ∈ cartesianDelta eta m := by
    intro t ht
    let y := AffineMap.lineMap (4 * rho / 5) (-(4 * rho / 5)) t
    have hy : y ∈ [[4 * rho / 5, -(4 * rho / 5)]] :=
      real_lineMap_mem_uIcc _ _ t ht
    have hmemb := (hleft y hy).1
    rw [hz₂left, hz₃left, complex_affine_lineMap_eq]
    simpa [y] using hmemb
  have hdelta₃ : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap z₃ z₄ t ∈ cartesianDelta eta m := by
    intro t ht
    let x := AffineMap.lineMap (-rho) (3 * rho / 5) t
    have hx : x ∈ [[-rho, 3 * rho / 5]] :=
      real_lineMap_mem_uIcc _ _ t ht
    have hmemb := (hbottom x hx).1
    rw [hz₃bottom, hz₄bottom, complex_affine_lineMap_eq]
    simpa [x] using hmemb
  have hdelta₄ : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap z₄ z₅ t ∈ cartesianDelta eta m := by
    intro t ht
    let x := AffineMap.lineMap rho M t
    have hx : x ∈ [[rho, M]] := real_lineMap_mem_uIcc _ _ t ht
    have hmemb := (hlower x hx).1
    rw [show AffineMap.lineMap z₄ z₅ t =
        1 + cartesianLowerDir * (x : ℂ) by
      dsimp [z₄, z₅, x]
      simpa using complex_affine_lineMap_eq
        (1 : ℂ) cartesianLowerDir rho M t]
    exact hmemb
  have h₀ := banachAffineAngularStripIdentity
    (F := F) (eta := eta) (m := m) (r := r) (n := n)
    (1 : ℂ) cartesianUpperDir M rho hm0 hr
    (by simpa [z₀, z₁] using hdelta₀)
    (by simpa [z₀, z₁] using hnorm₀)
    (by simpa [z₀, z₁] using hre₀) hH hF
  have h₁ := banachAffineAngularStripIdentity
    (F := F) (eta := eta) (m := m) (r := r) (n := n)
    (1 + (4 * rho / 5 : ℝ) * Complex.I) 1
      (3 * rho / 5) (-rho)
    hm0 hr
    (by simpa only [hz₁top, hz₂top] using hdelta₁)
    (by simpa only [hz₁top, hz₂top] using hnorm₁)
    (by simpa only [hz₁top, hz₂top] using hre₁) hH hF
  simp only [← hz₁top, ← hz₂top] at h₁
  have h₂ := banachAffineAngularStripIdentity
    (F := F) (eta := eta) (m := m) (r := r) (n := n)
    (1 - (rho : ℂ)) Complex.I
      (4 * rho / 5) (-(4 * rho / 5))
    hm0 hr
    (by simpa only [hz₂left, hz₃left] using hdelta₂)
    (by simpa only [hz₂left, hz₃left] using hnorm₂)
    (by simpa only [hz₂left, hz₃left] using hre₂) hH hF
  simp only [← hz₂left, ← hz₃left] at h₂
  have h₃ := banachAffineAngularStripIdentity
    (F := F) (eta := eta) (m := m) (r := r) (n := n)
    (1 - (4 * rho / 5 : ℝ) * Complex.I) 1
      (-rho) (3 * rho / 5)
    hm0 hr
    (by simpa only [hz₃bottom, hz₄bottom] using hdelta₃)
    (by simpa only [hz₃bottom, hz₄bottom] using hnorm₃)
    (by simpa only [hz₃bottom, hz₄bottom] using hre₃) hH hF
  simp only [← hz₃bottom, ← hz₄bottom] at h₃
  have h₄ := banachAffineAngularStripIdentity
    (F := F) (eta := eta) (m := m) (r := r) (n := n)
    (1 : ℂ) cartesianLowerDir rho M hm0 hr
    (by simpa [z₄, z₅] using hdelta₄)
    (by simpa [z₄, z₅] using hnorm₄)
    (by simpa [z₄, z₅] using hre₄) hH hF
  have h₅ := banachOuterMajorAngularStripIdentity
    (F := F) (eta := eta) (m := m) (r := r) (M := M) (n := n)
    hM hMeta hm0 hm43 hr
    (le_trans (by norm_num [r])
      (cartesianOuterRadius_gt_one hM).le) hH hF
  have hsum := six_radial_strips_telescope h₀ h₁ h₂ h₃ h₄ h₅
  let theta₀ := cartesianRightHalfAngle z₀
  let theta₁ := cartesianRightHalfAngle z₁
  let theta₂ := cartesianRightHalfAngle z₂
  let theta₃ := cartesianRightHalfAngle z₃
  let theta₄ := cartesianRightHalfAngle z₄
  let theta₅ := cartesianRightHalfAngle z₅
  have hlocalAngles :
      (∫ u in theta₀..theta₁, H u) +
        (∫ u in theta₁..theta₂, H u) +
        (∫ u in theta₂..theta₃, H u) +
        (∫ u in theta₃..theta₄, H u) +
        (∫ u in theta₄..theta₅, H u) =
          ∫ u in theta₀..theta₅, H u :=
    five_angular_intervals_telescope hH _ _ _ _ _ _
  have htheta₀ : theta₀ = cartesianOuterAngle M := by
    dsimp only [theta₀, z₀]
    rw [show cartesianUpperDir * (M : ℂ) =
        (M : ℂ) * cartesianUpperDir by ring]
    simpa only [cartesianOuterAngle] using
      (cartesianRightHalfAngle_eq_arg
        (z := (1 : ℂ) + (M : ℂ) * cartesianUpperDir) (by
          simp [cartesianUpperDir]
          positivity))
  have htheta₅ : theta₅ = -cartesianOuterAngle M := by
    have hright : cartesianRightHalfAngle z₅ =
        -cartesianRightHalfAngle z₀ := by
      dsimp [z₅, z₀, cartesianRightHalfAngle]
      rw [← Real.arctan_neg]
      congr 1
      simp [cartesianUpperDir, cartesianLowerDir]
      ring
    calc
      theta₅ = cartesianRightHalfAngle z₅ := rfl
      _ = -cartesianRightHalfAngle z₀ := hright
      _ = -theta₀ := rfl
      _ = -cartesianOuterAngle M := congrArg Neg.neg htheta₀
  have horient := full_circle_add_local_and_major_angles_eq_zero
    hH (banachCircleCoefficientPullback_periodic F r n)
      (cartesianOuterAngle M)
  have hcircle :
      (∮ z in C((0 : ℂ), r), banachCoefficientIntegrand F n z) =
        ∫ u in 0..2 * Real.pi, H u := by
    simpa [H] using
      (circleIntegral_eq_shifted_banachCircleCoefficientPullback
        F r 0 n)
  rw [hcircle]
  rw [← banachCartesianAffineBases_eq_localKeyhole]
  dsimp [banachCartesianAffineBases]
  dsimp [G, H, theta₀, theta₁, theta₂, theta₃, theta₄,
    theta₅] at h₀ h₁ h₂ h₃ h₄ h₅ hsum hlocalAngles
  rw [hlocalAngles] at hsum
  have hz₀angle : cartesianRightHalfAngle z₀ =
      cartesianOuterAngle M := by
    exact htheta₀
  have hz₅angle : cartesianRightHalfAngle z₅ =
      -cartesianOuterAngle M := by
    exact htheta₅
  rw [hz₀angle, hz₅angle] at hsum
  have hzero :
      (∫ u in 0..2 * Real.pi, H u) +
        ((∫ u in cartesianOuterAngle M..(-cartesianOuterAngle M), H u) +
          ∫ u in (2 * Real.pi - cartesianOuterAngle M)..
            cartesianOuterAngle M, H u) = 0 := by
    simpa only [add_assoc] using horient
  rw [hsum] at hzero
  simpa [G, H, rho, r, z₀, z₁, z₂, z₃, z₄, z₅,
    add_assoc] using hzero

end PerronWright.Transfer
