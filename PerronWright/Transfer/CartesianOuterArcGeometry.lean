import PerronWright.Transfer.BanachCartesianContourIdentity

/-!
An `n`-independent outer major arc for the Cartesian dent.

The arc is described intrinsically as the part of the circle through the
two truncated ray endpoints which lies to the left of those endpoints.
This avoids choosing an argument branch at the geometric stage.  Every
point of the arc lies in the punctured Cartesian Delta-domain and has
modulus uniformly larger than one.
-/

open Complex Set
noncomputable section

namespace PerronWright.Transfer

/-- Radius of the circle through the two ray endpoints at truncation `M`. -/
def cartesianOuterRadius (M : ℝ) : ℝ :=
  ‖(1 : ℂ) + (M : ℂ) * cartesianUpperDir‖

/-- The major arc of the endpoint circle, represented without choosing an
angular coordinate.  The complementary minor arc is precisely the part
which can meet the excluded right-pointing cone. -/
def cartesianOuterMajorArc (M : ℝ) : Set ℂ :=
  {z | ‖z‖ = cartesianOuterRadius M ∧ z.re ≤ 1 + 3 * M / 5}

theorem cartesianOuterRadius_sq (M : ℝ) :
    cartesianOuterRadius M ^ 2 = 1 + 6 * M / 5 + M ^ 2 := by
  rw [cartesianOuterRadius, ← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, cartesianUpperDir]
  ring

theorem cartesianOuterRadius_gt_one {M : ℝ} (hM : 0 < M) :
    1 < cartesianOuterRadius M := by
  have h :=
    (ray_geometry cartesianUpperDir norm_cartesianUpperDir
      cartesianUpperDir_re hM.le).2
  dsimp [cartesianOuterRadius]
  linarith

theorem cartesianOuterRadius_lt {M eta : ℝ}
    (hM : 0 < M) (hMeta : M < eta) :
    cartesianOuterRadius M < 1 + eta := by
  have htri := norm_add_le (1 : ℂ) ((M : ℂ) * cartesianUpperDir)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM,
    norm_cartesianUpperDir, mul_one, norm_one] at htri
  dsimp [cartesianOuterRadius]
  linarith

theorem cartesianUpperEndpoint_mem_outerMajorArc (M : ℝ) :
    (1 : ℂ) + (M : ℂ) * cartesianUpperDir ∈
      cartesianOuterMajorArc M := by
  constructor
  · rfl
  · simp [cartesianUpperDir]
    ring_nf
    rfl

theorem cartesianLowerEndpoint_mem_outerMajorArc (M : ℝ) :
    (1 : ℂ) + (M : ℂ) * cartesianLowerDir ∈
      cartesianOuterMajorArc M := by
  constructor
  · rw [cartesianOuterRadius, Complex.norm_def, Complex.norm_def]
    congr 1
    norm_num [Complex.normSq_apply, cartesianUpperDir, cartesianLowerDir]
  · simp [cartesianLowerDir]
    ring_nf
    rfl

/-- At every point of the major arc whose displacement from `1` has
nonnegative real part, its slope is at least `4/3`. -/
theorem cartesianOuterMajorArc_slope {M : ℝ} (hM : 0 < M)
    {z : ℂ} (hz : z ∈ cartesianOuterMajorArc M)
    (hx : 0 ≤ (z - 1).re) :
    (4 / 3 : ℝ) * (z - 1).re ≤ |(z - 1).im| := by
  let x : ℝ := (z - 1).re
  have hx0 : 0 ≤ x := hx
  have hxM : x ≤ 3 * M / 5 := by
    dsimp [x]
    linarith [hz.2]
  have hcircle :
      z.re ^ 2 + z.im ^ 2 = 1 + 6 * M / 5 + M ^ 2 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ = cartesianOuterRadius M ^ 2 := by rw [hz.1]
      _ = 1 + 6 * M / 5 + M ^ 2 := cartesianOuterRadius_sq M
  have hre : z.re = 1 + x := by
    dsimp [x]
    simp
  have hfac1 : 0 ≤ 3 * M - 5 * x := by linarith
  have hfac2 : 0 ≤ 15 * M + 25 * x + 18 := by positivity
  have hfac : 0 ≤ (3 * M - 5 * x) * (15 * M + 25 * x + 18) :=
    mul_nonneg hfac1 hfac2
  have hsq : ((4 / 3 : ℝ) * x) ^ 2 ≤ |z.im| ^ 2 := by
    rw [sq_abs]
    rw [hre] at hcircle
    nlinarith
  have habs : (4 / 3 : ℝ) * x ≤ |z.im| := by
    exact (sq_le_sq₀ (mul_nonneg (by norm_num) hx0)
      (abs_nonneg z.im)).mp hsq
  simpa only [x, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, sub_zero] using habs

/-- The intrinsic major arc lies wholly in the Cartesian dent. -/
theorem cartesianOuterMajorArc_subset_cartesianDelta
    {M eta m : ℝ} (hM : 0 < M) (hMeta : M < eta)
    (hm : m < 4 / 3) :
    cartesianOuterMajorArc M ⊆ cartesianDelta eta m := by
  intro z hz
  constructor
  · rw [hz.1]
    exact cartesianOuterRadius_lt hM hMeta
  · rintro ⟨hx, hy⟩
    have hslope := cartesianOuterMajorArc_slope hM hz hx
    let x : ℝ := (z - 1).re
    by_cases hxzero : x = 0
    · have hyzero : |(z - 1).im| = 0 := by
        apply le_antisymm
        · simpa only [x, hxzero, mul_zero] using hy
        · exact abs_nonneg _
      have hzre : z.re = 1 := by
        dsimp [x] at hxzero
        linarith
      have hzim : z.im = 0 := by
        apply abs_eq_zero.mp
        simpa using hyzero
      have hz1 : z = 1 := by
        apply Complex.ext
        · simpa only [Complex.one_re] using hzre
        · simpa only [Complex.one_im] using hzim
      have hradius := cartesianOuterRadius_gt_one hM
      have hone : 1 = cartesianOuterRadius M := by
        simpa only [hz1, norm_one] using hz.1
      linarith
    · have hxnonneg : 0 ≤ x := hx
      have hxpos : 0 < x := lt_of_le_of_ne hxnonneg (Ne.symm hxzero)
      have hstrict : m * x < (4 / 3 : ℝ) * x :=
        mul_lt_mul_of_pos_right hm hxpos
      exact (not_lt_of_ge hslope) (hy.trans_lt hstrict)

theorem cartesianOuterMajorArc_subset_puncturedDelta
    {M eta m : ℝ} (hM : 0 < M) (hMeta : M < eta)
    (hm : m < 4 / 3) :
    cartesianOuterMajorArc M ⊆
      cartesianDelta eta m \ {(0 : ℂ)} := by
  intro z hz
  refine ⟨cartesianOuterMajorArc_subset_cartesianDelta hM hMeta hm hz, ?_⟩
  simp only [mem_singleton_iff]
  intro hz0
  have hradius := cartesianOuterRadius_gt_one hM
  have h := hz.1
  rw [hz0, norm_zero] at h
  linarith

/-- Uniform modulus lower bound on the whole outer arc. -/
theorem cartesianOuterMajorArc_norm_lower {M : ℝ} (hM : 0 < M)
    {z : ℂ} (hz : z ∈ cartesianOuterMajorArc M) :
    1 + M / 2 ≤ ‖z‖ := by
  rw [hz.1]
  exact (ray_geometry cartesianUpperDir norm_cartesianUpperDir
    cartesianUpperDir_re hM.le).2

end PerronWright.Transfer
