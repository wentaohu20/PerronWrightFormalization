import PerronWright.Transfer.BanachCartesianDetour
import PerronWright.Transfer.BanachDeltaCauchy
import Mathlib.Topology.MetricSpace.Thickening

/-!
An exact, finite Cauchy--Goursat insertion of the admissible Cartesian
keyhole into a fixed Taylor circle.

This is deliberately a local contour identity, not the complete Delta
transfer theorem.  Each of the five affine pieces of the local keyhole is
thickened to an actual rectangle contained in `cartesianDelta \ {0}`.  The
other three sides of those rectangles form an explicit external closing
term.  Thus no contour-deformation or analytic-continuation hypothesis is
left as an interface.
-/

open Complex MeasureTheory Set Metric
open scoped Interval
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Banach-valued Cauchy coefficient integrand. -/
def banachCoefficientIntegrand (F : ℂ → E) (n : ℕ) (z : ℂ) : E :=
  z⁻¹ ^ (n + 1) • F z

/-- Integral on the base of a complex-affine rectangle.  The parameter is
real, while `q` is its complex tangent. -/
def banachAffineBaseIntegral (G : ℂ → E) (p q : ℂ) (a b : ℝ) : E :=
  ∫ x in a..b, q • G (p + q * (x : ℂ))

/-- The other three oriented sides of the affine rectangle whose base is
`banachAffineBaseIntegral G p q a b` and whose parameter-space height is
`ε`. -/
def banachAffineRectRemainder
    (G : ℂ → E) (p q : ℂ) (a b ε : ℝ) : E :=
  -(∫ x in a..b,
      q • G (p + q * ((x : ℂ) + (ε : ℂ) * I))) +
    I • (∫ y in (0 : ℝ)..ε,
      q • G (p + q * ((b : ℂ) + (y : ℂ) * I))) -
    I • (∫ y in (0 : ℝ)..ε,
      q • G (p + q * ((a : ℂ) + (y : ℂ) * I)))

private def affinePullback (G : ℂ → E) (p q : ℂ) (w : ℂ) : E :=
  q • G (p + q * w)

theorem banachAffineBase_add_remainder_eq_rectBoundary
    (G : ℂ → E) (p q : ℂ) (a b ε : ℝ) :
    banachAffineBaseIntegral G p q a b +
        banachAffineRectRemainder G p q a b ε =
      banachRectBoundary (affinePullback G p q) a b 0 ε := by
  simp only [banachAffineBaseIntegral, banachAffineRectRemainder,
    banachRectBoundary, affinePullback, ofReal_zero, zero_mul, add_zero]
  abel

/-- Cauchy--Goursat on a rotated and scaled affine rectangle. -/
theorem banachAffineBase_add_remainder_eq_zero
    {G : ℂ → E} {p q : ℂ} {a b ε : ℝ}
    (hG : ∀ w ∈ ([[a, b]] ×ℂ [[(0 : ℝ), ε]]),
      DifferentiableAt ℂ G (p + q * w)) :
    banachAffineBaseIntegral G p q a b +
        banachAffineRectRemainder G p q a b ε = 0 := by
  rw [banachAffineBase_add_remainder_eq_rectBoundary]
  apply banachRectBoundary_eq_zero_of_differentiableOn
  intro w hw
  have hφ : DifferentiableAt ℂ (fun z : ℂ => p + q * z) w := by
    fun_prop
  have hcomp : DifferentiableAt ℂ (G ∘ fun z : ℂ => p + q * z) w :=
    (hG w hw).comp w hφ
  change DifferentiableWithinAt ℂ
    (fun z : ℂ => q • G (p + q * z))
    ([[a, b]] ×ℂ [[(0 : ℝ), ε]]) w
  exact (hcomp.const_smul q).differentiableWithinAt

/-- The image of a compact affine segment has a genuine positive-width
rectangular neighborhood inside any prescribed open domain.  This theorem
is the finite geometric replacement for an abstract contour-deformation
assumption. -/
theorem exists_affineRect_remainder_eq_neg_base
    {G : ℂ → E} {U : Set ℂ} {p q : ℂ} {a b : ℝ}
    (hU : IsOpen U) (hq : ‖q‖ = 1)
    (hseg : ∀ x ∈ [[a, b]], p + q * (x : ℂ) ∈ U)
    (hG : DifferentiableOn ℂ G U) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w ∈ ([[a, b]] ×ℂ [[(0 : ℝ), ε]]), p + q * w ∈ U) ∧
      banachAffineBaseIntegral G p q a b +
        banachAffineRectRemainder G p q a b ε = 0 := by
  let K : Set ℂ := (fun x : ℝ => p + q * (x : ℂ)) '' [[a, b]]
  have hKcompact : IsCompact K := by
    exact isCompact_uIcc.image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact hseg x hx
  obtain ⟨δ, hδ, hthick⟩ :=
    hKcompact.exists_thickening_subset_open hU hKU
  let ε : ℝ := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hrect : ∀ w ∈ ([[a, b]] ×ℂ [[(0 : ℝ), ε]]), p + q * w ∈ U := by
    intro w hw
    have hεle : ε < δ := half_lt_self hδ
    have hwre : w.re ∈ [[a, b]] := hw.1
    have hwim : w.im ∈ Icc (0 : ℝ) ε := by
      have hwim' : w ∈ Complex.im ⁻¹' Icc (0 : ℝ) ε := by
        simpa only [uIcc_of_le hε.le] using hw.2
      exact hwim'
    let z₀ : ℂ := p + q * (w.re : ℂ)
    have hz₀K : z₀ ∈ K := ⟨w.re, hwre, rfl⟩
    have hdist : dist (p + q * w) z₀ < δ := by
      have hwdecomp : w = (w.re : ℂ) + (w.im : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [hwdecomp]
      dsimp [z₀]
      rw [dist_eq_norm]
      have heq :
          p + q * ((w.re : ℂ) + (w.im : ℂ) * I) -
              (p + q * (w.re : ℂ)) =
            q * ((w.im : ℂ) * I) := by ring
      rw [heq, norm_mul, hq, one_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_nonneg hwim.1]
      exact hwim.2.trans_lt hεle
    exact hthick (mem_thickening_iff.mpr ⟨z₀, hz₀K, hdist⟩)
  refine ⟨ε, hε, hrect, banachAffineBase_add_remainder_eq_zero ?_⟩
  intro w hw
  exact hG.differentiableAt (hU.mem_nhds (hrect w hw))

/-- The Cauchy coefficient integrand is holomorphic wherever both `F` is
holomorphic and the origin is absent. -/
theorem banachCoefficientIntegrand_differentiableOn
    {F : ℂ → E} {U : Set ℂ} {n : ℕ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hzero : (0 : ℂ) ∉ U) :
    DifferentiableOn ℂ (banachCoefficientIntegrand F n) U := by
  intro z hz
  have hz0 : z ≠ 0 := fun h => hzero (h ▸ hz)
  have hinv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z :=
    (differentiableAt_id.inv hz0)
  have hpow : DifferentiableAt ℂ (fun w : ℂ => w⁻¹ ^ (n + 1)) z :=
    hinv.pow _
  change DifferentiableWithinAt ℂ
    (fun w : ℂ => w⁻¹ ^ (n + 1) • F w) U z
  exact (hpow.smul
    (hF.differentiableAt (hU.mem_nhds hz))).differentiableWithinAt

/-! ### The five affine pieces and their exact orientation -/

/-- The sum of the five affine bases, in the boundary orientation used by
the Cartesian local keyhole.  The upper ray is traversed inward, then the
three sides of the `U`-detour are traversed from top to bottom, and the lower
ray is traversed outward. -/
def banachCartesianAffineBases (F : ℂ → E) (M : ℝ) (n : ℕ) : E :=
  let ρ := cartesianDetourRadius n
  let G := banachCoefficientIntegrand F n
  banachAffineBaseIntegral G 1 cartesianUpperDir M ρ +
    banachAffineBaseIntegral G (1 + (4 * ρ / 5 : ℝ) * I) 1
      (3 * ρ / 5) (-ρ) +
    banachAffineBaseIntegral G (1 - (ρ : ℂ)) I
      (4 * ρ / 5) (-(4 * ρ / 5)) +
    banachAffineBaseIntegral G (1 - (4 * ρ / 5 : ℝ) * I) 1
      (-ρ) (3 * ρ / 5) +
    banachAffineBaseIntegral G 1 cartesianLowerDir ρ M

/-- Expanding the five affine parametrizations gives exactly the previously
defined Cartesian local keyhole, including all orientations. -/
theorem banachCartesianAffineBases_eq_localKeyhole
    (F : ℂ → E) (M : ℝ) (n : ℕ) :
    banachCartesianAffineBases F M n =
      banachCartesianLocalKeyhole F M n := by
  let rho := cartesianDetourRadius n
  let G := banachCoefficientIntegrand F n
  have hUpper :
      banachAffineBaseIntegral G 1 cartesianUpperDir M rho =
        -( ∫ t in rho..M,
          (cartesianUpperDir *
            (((1 : ℂ) + (t : ℂ) * cartesianUpperDir)⁻¹ ^ (n + 1))) •
              F ((1 : ℂ) + (t : ℂ) * cartesianUpperDir)) := by
    rw [banachAffineBaseIntegral, intervalIntegral.integral_symm]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [G, banachCoefficientIntegrand]
    rw [smul_smul]
    congr 2 <;> ring_nf
  have hTop :
      banachAffineBaseIntegral G (1 + (4 * rho / 5 : ℝ) * I) 1
          (3 * rho / 5) (-rho) =
        -(∫ x in (-rho)..(3 * rho / 5),
          (cartesianDetourTop rho x)⁻¹ ^ (n + 1) •
            F (cartesianDetourTop rho x)) := by
    rw [banachAffineBaseIntegral, intervalIntegral.integral_symm]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [G, banachCoefficientIntegrand]
    rw [one_smul]
    congr 2 <;> simp [cartesianDetourTop] <;> ring_nf
  have hLeft :
      banachAffineBaseIntegral G (1 - (rho : ℂ)) I
          (4 * rho / 5) (-(4 * rho / 5)) =
        -(I • (∫ y in (-(4 * rho / 5))..(4 * rho / 5),
          (cartesianDetourLeft rho y)⁻¹ ^ (n + 1) •
            F (cartesianDetourLeft rho y))) := by
    rw [banachAffineBaseIntegral, intervalIntegral.integral_symm,
      ← intervalIntegral.integral_smul]
    congr 1
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [G, banachCoefficientIntegrand]
    congr 2 <;> simp [cartesianDetourLeft] <;> ring_nf
  have hBottom :
      banachAffineBaseIntegral G (1 - (4 * rho / 5 : ℝ) * I) 1
          (-rho) (3 * rho / 5) =
        ∫ x in (-rho)..(3 * rho / 5),
          (cartesianDetourBottom rho x)⁻¹ ^ (n + 1) •
            F (cartesianDetourBottom rho x) := by
    rw [banachAffineBaseIntegral]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [G, banachCoefficientIntegrand]
    rw [one_smul]
    congr 2 <;> simp [cartesianDetourBottom] <;> ring_nf
  have hLower :
      banachAffineBaseIntegral G 1 cartesianLowerDir rho M =
        ∫ t in rho..M,
          (cartesianLowerDir *
            (((1 : ℂ) + (t : ℂ) * cartesianLowerDir)⁻¹ ^ (n + 1))) •
              F ((1 : ℂ) + (t : ℂ) * cartesianLowerDir) := by
    rw [banachAffineBaseIntegral]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [G, banachCoefficientIntegrand]
    rw [smul_smul]
    congr 2 <;> ring_nf
  dsimp [banachCartesianAffineBases, banachCartesianLocalKeyhole,
    banachCartesianDetour, rho, G]
  rw [hUpper, hTop, hLeft, hBottom, hLower]
  abel

/-- The sum of the other three sides of the five affine rectangles. -/
def banachCartesianRectRemainders
    (F : ℂ → E) (M : ℝ) (n : ℕ)
    (εUpper εTop εLeft εBottom εLower : ℝ) : E :=
  let ρ := cartesianDetourRadius n
  let G := banachCoefficientIntegrand F n
  banachAffineRectRemainder G 1 cartesianUpperDir M ρ εUpper +
    banachAffineRectRemainder G (1 + (4 * ρ / 5 : ℝ) * I) 1
      (3 * ρ / 5) (-ρ) εTop +
    banachAffineRectRemainder G (1 - (ρ : ℂ)) I
      (4 * ρ / 5) (-(4 * ρ / 5)) εLeft +
    banachAffineRectRemainder G (1 - (4 * ρ / 5 : ℝ) * I) 1
      (-ρ) (3 * ρ / 5) εBottom +
    banachAffineRectRemainder G 1 cartesianLowerDir ρ M εLower

/-- The fixed Taylor circle together with the fifteen non-base sides of the
five affine rectangles.  This is an explicit outer closing term: no
deformation theorem is hidden in the definition. -/
def banachCartesianExternalClosure
    (F : ℂ → E) (R M : ℝ) (n : ℕ)
    (εUpper εTop εLeft εBottom εLower : ℝ) : E :=
  (∮ z in C((0 : ℂ), R), banachCoefficientIntegrand F n z) +
    banachCartesianRectRemainders F M n
      εUpper εTop εLeft εBottom εLower

/-- Every one of the five positively thickened affine rectangles stays in
the prescribed open domain.  The interval endpoints record the boundary
orientation, rather than merely the underlying unoriented segments. -/
def banachCartesianRectanglesAdmissible
    (U : Set ℂ) (M : ℝ) (n : ℕ)
    (εUpper εTop εLeft εBottom εLower : ℝ) : Prop :=
  let ρ := cartesianDetourRadius n
  (∀ w ∈ ([[M, ρ]] ×ℂ [[(0 : ℝ), εUpper]]),
      1 + cartesianUpperDir * w ∈ U) ∧
  (∀ w ∈ ([[3 * ρ / 5, -ρ]] ×ℂ [[(0 : ℝ), εTop]]),
      1 + (4 * ρ / 5 : ℝ) * I + w ∈ U) ∧
  (∀ w ∈ ([[4 * ρ / 5, -(4 * ρ / 5)]] ×ℂ
      [[(0 : ℝ), εLeft]]),
      1 - (ρ : ℂ) + I * w ∈ U) ∧
  (∀ w ∈ ([[-ρ, 3 * ρ / 5]] ×ℂ [[(0 : ℝ), εBottom]]),
      1 - (4 * ρ / 5 : ℝ) * I + w ∈ U) ∧
  (∀ w ∈ ([[(ρ : ℝ), M]] ×ℂ [[(0 : ℝ), εLower]]),
      1 + cartesianLowerDir * w ∈ U)

private theorem cartesianDetourRadius_pos {n : ℕ} (hn : 0 < n) :
    0 < cartesianDetourRadius n := by
  dsimp [cartesianDetourRadius]
  positivity

private theorem two_cartesianDetourRadius_lt {n : ℕ} {eta : ℝ}
    (hn : 0 < n) (heta : 1 / (n : ℝ) < eta) :
    2 * cartesianDetourRadius n < eta := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn'
  calc
    2 * cartesianDetourRadius n = (1 / (n : ℝ)) / 2 := by
      dsimp [cartesianDetourRadius]
      ring
    _ < 1 / (n : ℝ) := half_lt_self hinv
    _ < eta := heta

private theorem two_cartesianDetourRadius_lt_one {n : ℕ} (hn : 0 < n) :
    2 * cartesianDetourRadius n < 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  rw [show 2 * cartesianDetourRadius n = 1 / (2 * (n : ℝ)) by
    dsimp [cartesianDetourRadius]
    ring]
  rw [div_lt_one (by positivity : (0 : ℝ) < 2 * n)]
  linarith

/-- Every oriented base segment of the local Cartesian keyhole lies in the
punctured Cartesian Delta-domain. -/
theorem banachCartesianLocalKeyhole_segments_mem
    {M eta m : ℝ} {n : ℕ}
    (hn : 0 < n) (hrhoM : cartesianDetourRadius n ≤ M)
    (hMeta : M < eta) (heta : 1 / (n : ℝ) < eta)
    (hm : m < 4 / 3) :
    let rho := cartesianDetourRadius n
    let U := cartesianDelta eta m \ {(0 : ℂ)}
    (∀ t ∈ [[M, rho]], 1 + cartesianUpperDir * (t : ℂ) ∈ U) ∧
    (∀ x ∈ [[3 * rho / 5, -rho]],
      1 + (4 * rho / 5 : ℝ) * I + (x : ℂ) ∈ U) ∧
    (∀ y ∈ [[4 * rho / 5, -(4 * rho / 5)]],
      1 - (rho : ℂ) + I * (y : ℂ) ∈ U) ∧
    (∀ x ∈ [[-rho, 3 * rho / 5]],
      1 - (4 * rho / 5 : ℝ) * I + (x : ℂ) ∈ U) ∧
    (∀ t ∈ [[rho, M]], 1 + cartesianLowerDir * (t : ℂ) ∈ U) := by
  let rho := cartesianDetourRadius n
  let U := cartesianDelta eta m \ {(0 : ℂ)}
  have hrho : 0 < rho := cartesianDetourRadius_pos hn
  have hrhoeta : 2 * rho < eta := two_cartesianDetourRadius_lt hn heta
  have hrho1 : 2 * rho < 1 := two_cartesianDetourRadius_lt_one hn
  have hupper : ∀ t ∈ [[M, rho]],
      1 + cartesianUpperDir * (t : ℂ) ∈ U := by
    intro t ht
    have ht' : t ∈ Icc rho M := by
      rw [uIcc_of_ge hrhoM] at ht
      exact ht
    have ht0 : 0 < t := hrho.trans_le ht'.1
    have hteta : t < eta := ht'.2.trans_lt hMeta
    constructor
    · simpa only [mul_comm] using
        ray_mem_cartesianDelta cartesianUpperDir norm_cartesianUpperDir
          cartesianUpperDir_re cartesianUpperDir_abs_im ht0 hteta hm
    · simp only [mem_singleton_iff]
      intro hz
      have hre := congrArg Complex.re hz
      simp [cartesianUpperDir] at hre
      linarith
  have hlower : ∀ t ∈ [[rho, M]],
      1 + cartesianLowerDir * (t : ℂ) ∈ U := by
    intro t ht
    have ht' : t ∈ Icc rho M := by
      rw [uIcc_of_le hrhoM] at ht
      exact ht
    have ht0 : 0 < t := hrho.trans_le ht'.1
    have hteta : t < eta := ht'.2.trans_lt hMeta
    constructor
    · simpa only [mul_comm] using
        ray_mem_cartesianDelta cartesianLowerDir norm_cartesianLowerDir
          cartesianLowerDir_re cartesianLowerDir_abs_im ht0 hteta hm
    · simp only [mem_singleton_iff]
      intro hz
      have hre := congrArg Complex.re hz
      simp [cartesianLowerDir] at hre
      linarith
  have htop : ∀ x ∈ [[3 * rho / 5, -rho]],
      1 + (4 * rho / 5 : ℝ) * I + (x : ℂ) ∈ U := by
    intro x hx
    have hx' : x ∈ Icc (-rho) (3 * rho / 5) := by
      have horder : -rho ≤ 3 * rho / 5 := by linarith
      rw [uIcc_of_ge horder] at hx
      exact hx
    have hmem := cartesianDetourTop_mem hm hrho hrhoeta hx'
    have hdist := cartesianDetourTop_dist_le hrho.le hx'
    have hne : cartesianDetourTop rho x ≠ 0 := by
      intro hz
      rw [hz] at hdist
      norm_num at hdist
      linarith
    have hzU : cartesianDetourTop rho x ∈ U :=
      ⟨hmem, by simpa only [mem_singleton_iff] using hne⟩
    have heq :
        1 + (4 * rho / 5 : ℝ) * I + (x : ℂ) =
          cartesianDetourTop rho x := by
      simp [cartesianDetourTop]
      ring
    rw [heq]
    exact hzU
  have hleft : ∀ y ∈ [[4 * rho / 5, -(4 * rho / 5)]],
      1 - (rho : ℂ) + I * (y : ℂ) ∈ U := by
    intro y hy
    have hy' : y ∈ Icc (-(4 * rho / 5)) (4 * rho / 5) := by
      have horder : -(4 * rho / 5) ≤ 4 * rho / 5 := by linarith
      rw [uIcc_of_ge horder] at hy
      exact hy
    have hmem := cartesianDetourLeft_mem (m := m) hrho hrhoeta hy'
    have hdist := cartesianDetourLeft_dist_le hrho.le hy'
    have hne : cartesianDetourLeft rho y ≠ 0 := by
      intro hz
      rw [hz] at hdist
      norm_num at hdist
      linarith
    simpa only [cartesianDetourLeft, mul_comm] using
      (show cartesianDetourLeft rho y ∈ U from
        ⟨hmem, by simpa only [mem_singleton_iff] using hne⟩)
  have hbottom : ∀ x ∈ [[-rho, 3 * rho / 5]],
      1 - (4 * rho / 5 : ℝ) * I + (x : ℂ) ∈ U := by
    intro x hx
    have hx' : x ∈ Icc (-rho) (3 * rho / 5) := by
      have horder : -rho ≤ 3 * rho / 5 := by linarith
      rw [uIcc_of_le horder] at hx
      exact hx
    have hmem := cartesianDetourBottom_mem hm hrho hrhoeta hx'
    have hdist := cartesianDetourBottom_dist_le hrho.le hx'
    have hne : cartesianDetourBottom rho x ≠ 0 := by
      intro hz
      rw [hz] at hdist
      norm_num at hdist
      linarith
    have hzU : cartesianDetourBottom rho x ∈ U :=
      ⟨hmem, by simpa only [mem_singleton_iff] using hne⟩
    have heq :
        1 - (4 * rho / 5 : ℝ) * I + (x : ℂ) =
          cartesianDetourBottom rho x := by
      simp [cartesianDetourBottom]
      ring
    rw [heq]
    exact hzU
  exact ⟨hupper, htop, hleft, hbottom, hlower⟩

/-! ### Exact local insertion into a fixed circle -/

/-- The fixed Cauchy circle is exactly the oriented Cartesian local
keyhole plus an explicit outer closure made of the other sides of five
genuine rectangles.  The result returns both the positive widths and the
full rectangle-containment certificate in `cartesianDelta eta m \ {0}`.

This is the finite Cauchy--Goursat step needed before any outer-contour
estimate.  It does not assume or assert an abstract contour deformation. -/
theorem exists_banachCartesianContourIdentity
    [CompleteSpace E]
    {F : ℂ → E} {R M eta m : ℝ} {n : ℕ}
    (hn : 0 < n) (hrhoM : cartesianDetourRadius n ≤ M)
    (hMeta : M < eta) (heta : 1 / (n : ℝ) < eta)
    (hm : m < 4 / 3)
    (hF : DifferentiableOn ℂ F (cartesianDelta eta m)) :
    ∃ εUpper εTop εLeft εBottom εLower : ℝ,
      0 < εUpper ∧ 0 < εTop ∧ 0 < εLeft ∧
      0 < εBottom ∧ 0 < εLower ∧
      banachCartesianRectanglesAdmissible
        (cartesianDelta eta m \ {(0 : ℂ)}) M n
        εUpper εTop εLeft εBottom εLower ∧
      (∮ z in C((0 : ℂ), R), banachCoefficientIntegrand F n z) =
        banachCartesianLocalKeyhole F M n +
          banachCartesianExternalClosure F R M n
            εUpper εTop εLeft εBottom εLower := by
  let rho := cartesianDetourRadius n
  let U := cartesianDelta eta m \ {(0 : ℂ)}
  let G := banachCoefficientIntegrand F n
  have hU : IsOpen U :=
    (isOpen_cartesianDelta eta m).sdiff isClosed_singleton
  have hzero : (0 : ℂ) ∉ U := by
    simp [U]
  have hG : DifferentiableOn ℂ G U := by
    exact banachCoefficientIntegrand_differentiableOn hU
      (hF.mono sdiff_subset) hzero
  obtain ⟨hupper, htop, hleft, hbottom, hlower⟩ :=
    banachCartesianLocalKeyhole_segments_mem hn hrhoM hMeta heta hm
  obtain ⟨εUpper, hεUpper, hrectUpper, heqUpper⟩ :=
    exists_affineRect_remainder_eq_neg_base hU norm_cartesianUpperDir
      hupper hG
  obtain ⟨εTop, hεTop, hrectTop, heqTop⟩ :=
    exists_affineRect_remainder_eq_neg_base hU (by norm_num)
      (p := 1 + (4 * rho / 5 : ℝ) * I) (q := 1)
      (a := 3 * rho / 5) (b := -rho) (by
        intro x hx
        simpa only [one_mul, add_assoc] using htop x hx) hG
  obtain ⟨εLeft, hεLeft, hrectLeft, heqLeft⟩ :=
    exists_affineRect_remainder_eq_neg_base hU Complex.norm_I
      (p := 1 - (rho : ℂ)) (q := I)
      (a := 4 * rho / 5) (b := -(4 * rho / 5)) (by
        intro y hy
        simpa only [mul_comm] using hleft y hy) hG
  obtain ⟨εBottom, hεBottom, hrectBottom, heqBottom⟩ :=
    exists_affineRect_remainder_eq_neg_base hU (by norm_num)
      (p := 1 - (4 * rho / 5 : ℝ) * I) (q := 1)
      (a := -rho) (b := 3 * rho / 5) (by
        intro x hx
        simpa only [one_mul, add_assoc] using hbottom x hx) hG
  obtain ⟨εLower, hεLower, hrectLower, heqLower⟩ :=
    exists_affineRect_remainder_eq_neg_base hU norm_cartesianLowerDir
      hlower hG
  refine ⟨εUpper, εTop, εLeft, εBottom, εLower,
    hεUpper, hεTop, hεLeft, hεBottom, hεLower, ?_, ?_⟩
  · dsimp [banachCartesianRectanglesAdmissible]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [rho, U] using hrectUpper
    · simpa only [rho, U, one_mul] using hrectTop
    · simpa only [rho, U] using hrectLeft
    · simpa only [rho, U, one_mul] using hrectBottom
    · simpa only [rho, U] using hrectLower
  · have hremUpper := eq_neg_of_add_eq_zero_right heqUpper
    have hremTop := eq_neg_of_add_eq_zero_right heqTop
    have hremLeft := eq_neg_of_add_eq_zero_right heqLeft
    have hremBottom := eq_neg_of_add_eq_zero_right heqBottom
    have hremLower := eq_neg_of_add_eq_zero_right heqLower
    have hrems :
        banachCartesianRectRemainders F M n
            εUpper εTop εLeft εBottom εLower =
          -banachCartesianAffineBases F M n := by
      dsimp [banachCartesianRectRemainders, banachCartesianAffineBases,
        rho, G] at hremUpper hremTop hremLeft hremBottom hremLower ⊢
      rw [hremUpper, hremTop, hremLeft, hremBottom, hremLower]
      abel
    rw [banachCartesianExternalClosure, hrems,
      ← banachCartesianAffineBases_eq_localKeyhole]
    abel

/-- Cauchy's formula turns the preceding exact circle identity into an
exact Taylor-coefficient identity.  The only additional input is ordinary
holomorphy on the fixed Cauchy disc. -/
theorem exists_banachTaylorCoefficient_cartesianContourIdentity
    [CompleteSpace E]
    {F : ℂ → E} {R M eta m : ℝ} {n : ℕ}
    (hR : 0 < R)
    (hn : 0 < n) (hrhoM : cartesianDetourRadius n ≤ M)
    (hMeta : M < eta) (heta : 1 / (n : ℝ) < eta)
    (hm : m < 4 / 3)
    (hFdelta : DifferentiableOn ℂ F (cartesianDelta eta m))
    (hFdisc : DifferentiableOn ℂ F (Metric.closedBall 0 R)) :
    ∃ εUpper εTop εLeft εBottom εLower : ℝ,
      0 < εUpper ∧ 0 < εTop ∧ 0 < εLeft ∧
      0 < εBottom ∧ 0 < εLower ∧
      banachCartesianRectanglesAdmissible
        (cartesianDelta eta m \ {(0 : ℂ)}) M n
        εUpper εTop εLeft εBottom εLower ∧
      (2 * Real.pi * I) • banachTaylorCoefficient F n =
        banachCartesianLocalKeyhole F M n +
          banachCartesianExternalClosure F R M n
            εUpper εTop εLeft εBottom εLower := by
  obtain ⟨εUpper, εTop, εLeft, εBottom, εLower,
      hεUpper, hεTop, hεLeft, hεBottom, hεLower,
      hrect, hid⟩ :=
    exists_banachCartesianContourIdentity
      (R := R) hn hrhoM hMeta heta hm hFdelta
  refine ⟨εUpper, εTop, εLeft, εBottom, εLower,
    hεUpper, hεTop, hεLeft, hεBottom, hεLower, hrect, ?_⟩
  rw [← circleIntegral_eq_banachTaylorCoefficient hR hFdisc n]
  exact hid

end PerronWright.Transfer
