import PerronWright.Transfer.BanachContourBounds

/-!
An admissible inner detour for the Cartesian dent.

The full circle about `1` used in a preliminary keyhole estimate crosses the
excluded cone, so a bound on `cartesianDelta` does not control that circle.
Here it is replaced by three line segments which stay outside the cone.  The
result is an actual Banach-valued `n^(-a-1)` local-contour estimate obtained
solely from the power bound on `cartesianDelta`.
-/

open Real MeasureTheory Set
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Banach-valued Laplace estimate remains valid after deleting an
initial interval.  This is the form used by a genuine keyhole ray, whose
inner endpoint is separated from the singularity. -/
theorem banach_norm_radial_integral_from_le
    {a ρ M c : ℝ} {n : ℕ} {f : ℝ → E}
    (ha : -1 < a) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hc : 0 < c) (hn : 0 < n)
    (hbound : ∀ t ∈ Ioc ρ M,
      ‖f t‖ ≤ t ^ a * Real.exp (-(c * (n : ℝ) * t))) :
    ‖∫ t in ρ..M, f t‖ ≤
      (1 / (c * n)) ^ (a + 1) * Gamma (a + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hrate : 0 < c * (n : ℝ) := mul_pos hc hn'
  have ha' : 0 < a + 1 := by linarith
  have hkey := Real.integral_rpow_mul_exp_neg_mul_Ioi ha' hrate
  have hint : IntegrableOn
      (fun t : ℝ => t ^ ((a + 1) - 1) * Real.exp (-((c * n) * t)))
      (Ioi 0) := .of_integral_ne_zero (by
        rw [hkey]
        exact (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hrate) _)
          (Real.Gamma_pos_of_pos ha')).ne')
  have hmajor0 : IntervalIntegrable
      (fun t : ℝ => t ^ a * Real.exp (-(c * (n : ℝ) * t)))
      volume 0 M := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hρ.trans hρM)]
    simpa only [add_sub_cancel_right] using hint.mono_set Ioc_subset_Ioi_self
  have hmajorρ : IntervalIntegrable
      (fun t : ℝ => t ^ a * Real.exp (-(c * (n : ℝ) * t)))
      volume ρ M := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hρM]
    simpa only [add_sub_cancel_right] using hint.mono_set
      (fun t ht => lt_of_le_of_lt hρ ht.1)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hρM
    (Filter.Eventually.of_forall (fun t ht => hbound t ht)) hmajorρ
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) M)]
      (fun t : ℝ => t ^ a * Real.exp (-(c * (n : ℝ) * t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le
  have hmono := intervalIntegral.integral_mono_interval hρ hρM le_rfl
    hnonneg hmajor0
  exact hnorm.trans (hmono.trans (laplace_ray_bound ha (hρ.trans hρM) hc hn))

/-- Public versions of the two rational unit directions used by the
Cartesian keyhole. -/
def cartesianUpperDir : ℂ := ⟨3 / 5, 4 / 5⟩

def cartesianLowerDir : ℂ := ⟨3 / 5, -(4 / 5)⟩

@[simp] theorem norm_cartesianUpperDir : ‖cartesianUpperDir‖ = 1 := by
  rw [Complex.norm_def]
  norm_num [cartesianUpperDir, Complex.normSq_apply]

@[simp] theorem norm_cartesianLowerDir : ‖cartesianLowerDir‖ = 1 := by
  rw [Complex.norm_def]
  norm_num [cartesianLowerDir, Complex.normSq_apply]

@[simp] theorem cartesianUpperDir_re : cartesianUpperDir.re = 3 / 5 := rfl
@[simp] theorem cartesianLowerDir_re : cartesianLowerDir.re = 3 / 5 := rfl

@[simp] theorem cartesianUpperDir_abs_im : |cartesianUpperDir.im| = 4 / 5 := by
  norm_num [cartesianUpperDir]

@[simp] theorem cartesianLowerDir_abs_im : |cartesianLowerDir.im| = 4 / 5 := by
  norm_num [cartesianLowerDir]

/-- A truncated ray contribution is controlled directly by the power bound
on `cartesianDelta`; both ray membership and the Cauchy denominator estimate
are discharged inside the proof. -/
theorem banach_radial_piece_from_on_cartesianDelta
    {F : ℂ → E} {d : ℂ} {ρ M a η m : ℝ} {n : ℕ}
    (hd : ‖d‖ = 1) (hdre : d.re = 3 / 5)
    (hdim : |d.im| = 4 / 5)
    (hρ : 0 ≤ ρ) (hρM : ρ ≤ M) (hM1 : M ≤ 1)
    (hMη : M < η) (hm : m < 4 / 3) (ha : -1 < a) (hn : 0 < n)
    (hF : ∀ z ∈ cartesianDelta η m,
      ‖F z‖ ≤ ‖z - 1‖ ^ a) :
    ‖∫ t in ρ..M,
        (d * (((1 : ℂ) + (t : ℂ) * d)⁻¹ ^ (n + 1))) •
          F ((1 : ℂ) + (t : ℂ) * d)‖ ≤
      (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) := by
  apply banach_norm_radial_integral_from_le ha hρ hρM (by norm_num) hn
  intro t ht
  have ht0 : 0 ≤ t := hρ.trans ht.1.le
  have ht1 : t ≤ 1 := ht.2.trans hM1
  have htη : t < η := ht.2.trans_lt hMη
  have hmem : (1 : ℂ) + (t : ℂ) * d ∈ cartesianDelta η m :=
    ray_mem_cartesianDelta d hd hdre hdim (lt_of_le_of_lt hρ ht.1) htη hm
  have hdist : ‖((1 : ℂ) + (t : ℂ) * d) - 1‖ = t := by
    rw [norm_sub_rev]
    exact (ray_geometry d hd hdre ht0).1
  have hden : ‖((1 : ℂ) + (t : ℂ) * d)⁻¹ ^ (n + 1)‖ ≤
      Real.exp (-((n : ℝ) * t / 4)) :=
    ray_inverse_pow_bound d hd hdre ht0 ht1 n
  calc
    ‖(d * ((1 + (t : ℂ) * d)⁻¹ ^ (n + 1))) •
        F (1 + (t : ℂ) * d)‖ =
      ‖F (1 + (t : ℂ) * d)‖ *
        ‖(1 + (t : ℂ) * d)⁻¹ ^ (n + 1)‖ := by
          rw [norm_smul, norm_mul, hd, one_mul, mul_comm]
    _ ≤ t ^ a * Real.exp (-((n : ℝ) * t / 4)) :=
      mul_le_mul (by simpa only [hdist] using hF _ hmem) hden
        (norm_nonneg _) (Real.rpow_nonneg ht0 _)
    _ = t ^ a * Real.exp (-((1 / 4 : ℝ) * (n : ℝ) * t)) := by
      congr 1
      ring_nf

/-- The local scale used by the polygonal detour. -/
def cartesianDetourRadius (n : ℕ) : ℝ := 1 / (4 * (n : ℝ))

/-- Upper horizontal side of the local detour. -/
def cartesianDetourTop (ρ x : ℝ) : ℂ :=
  1 + (x : ℂ) + ((4 * ρ / 5 : ℝ) : ℂ) * Complex.I

/-- Lower horizontal side of the local detour. -/
def cartesianDetourBottom (ρ x : ℝ) : ℂ :=
  1 + (x : ℂ) - ((4 * ρ / 5 : ℝ) : ℂ) * Complex.I

/-- Left vertical side of the local detour. -/
def cartesianDetourLeft (ρ y : ℝ) : ℂ :=
  1 - (ρ : ℂ) + (y : ℂ) * Complex.I

private theorem abs_le_radius_of_mem {ρ x : ℝ} (hρ : 0 ≤ ρ)
    (hx : x ∈ Icc (-ρ) (3 * ρ / 5)) : |x| ≤ ρ := by
  rw [abs_le]
  constructor
  · exact hx.1
  · exact hx.2.trans (by linarith)

theorem cartesianDetourTop_dist_le {ρ x : ℝ} (hρ : 0 ≤ ρ)
    (hx : x ∈ Icc (-ρ) (3 * ρ / 5)) :
    ‖cartesianDetourTop ρ x - 1‖ ≤ 2 * ρ := by
  have hxabs := abs_le_radius_of_mem hρ hx
  have hfour : 0 ≤ 4 * ρ / 5 := by positivity
  calc
    ‖cartesianDetourTop ρ x - 1‖ ≤
        |(cartesianDetourTop ρ x - 1).re| +
          |(cartesianDetourTop ρ x - 1).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |x| + 4 * ρ / 5 := by
      simp [cartesianDetourTop, abs_of_nonneg hfour]
    _ ≤ 2 * ρ := by linarith

theorem cartesianDetourBottom_dist_le {ρ x : ℝ} (hρ : 0 ≤ ρ)
    (hx : x ∈ Icc (-ρ) (3 * ρ / 5)) :
    ‖cartesianDetourBottom ρ x - 1‖ ≤ 2 * ρ := by
  have hxabs := abs_le_radius_of_mem hρ hx
  have hfour : 0 ≤ 4 * ρ / 5 := by positivity
  calc
    ‖cartesianDetourBottom ρ x - 1‖ ≤
        |(cartesianDetourBottom ρ x - 1).re| +
          |(cartesianDetourBottom ρ x - 1).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |x| + 4 * ρ / 5 := by
      simp [cartesianDetourBottom, abs_of_nonneg hfour]
    _ ≤ 2 * ρ := by linarith

theorem cartesianDetourLeft_dist_le {ρ y : ℝ} (hρ : 0 ≤ ρ)
    (hy : y ∈ Icc (-(4 * ρ / 5)) (4 * ρ / 5)) :
    ‖cartesianDetourLeft ρ y - 1‖ ≤ 2 * ρ := by
  have hyabs : |y| ≤ 4 * ρ / 5 := by
    rw [abs_le]
    exact hy
  calc
    ‖cartesianDetourLeft ρ y - 1‖ ≤
        |(cartesianDetourLeft ρ y - 1).re| +
          |(cartesianDetourLeft ρ y - 1).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = ρ + |y| := by
      simp [cartesianDetourLeft, abs_of_nonneg hρ]
    _ ≤ 2 * ρ := by linarith

/-- Every point of the upper segment is in the genuine Cartesian dent. -/
theorem cartesianDetourTop_mem {η m ρ x : ℝ}
    (hm : m < 4 / 3) (hρ : 0 < ρ)
    (hρη : 2 * ρ < η) (hx : x ∈ Icc (-ρ) (3 * ρ / 5)) :
    cartesianDetourTop ρ x ∈ cartesianDelta η m := by
  have hdist := cartesianDetourTop_dist_le hρ.le hx
  constructor
  · have htri : ‖cartesianDetourTop ρ x‖ ≤
        ‖cartesianDetourTop ρ x - 1‖ + 1 := by
      calc
        ‖cartesianDetourTop ρ x‖ =
            ‖(cartesianDetourTop ρ x - 1) + 1‖ := by congr 1; ring
        _ ≤ _ := by simpa only [norm_one] using
          norm_add_le (cartesianDetourTop ρ x - 1) (1 : ℂ)
    linarith
  · intro hc
    have hx0 : 0 ≤ x := by
      simpa [cartesianDetourTop] using hc.1
    have him : 4 * ρ / 5 ≤ m * x := by
      have hfour : 0 ≤ 4 * ρ / 5 := by positivity
      simpa [cartesianDetourTop, abs_of_nonneg hfour] using hc.2
    by_cases hxz : x = 0
    · subst x
      norm_num at him
      linarith
    · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxz)
      have hmx : m * x < (4 / 3 : ℝ) * x :=
        mul_lt_mul_of_pos_right hm hxpos
      nlinarith [hx.2]

/-- Every point of the lower segment is in the genuine Cartesian dent. -/
theorem cartesianDetourBottom_mem {η m ρ x : ℝ}
    (hm : m < 4 / 3) (hρ : 0 < ρ)
    (hρη : 2 * ρ < η) (hx : x ∈ Icc (-ρ) (3 * ρ / 5)) :
    cartesianDetourBottom ρ x ∈ cartesianDelta η m := by
  have hdist := cartesianDetourBottom_dist_le hρ.le hx
  constructor
  · have htri : ‖cartesianDetourBottom ρ x‖ ≤
        ‖cartesianDetourBottom ρ x - 1‖ + 1 := by
      calc
        ‖cartesianDetourBottom ρ x‖ =
            ‖(cartesianDetourBottom ρ x - 1) + 1‖ := by congr 1; ring
        _ ≤ _ := by simpa only [norm_one] using
          norm_add_le (cartesianDetourBottom ρ x - 1) (1 : ℂ)
    linarith
  · intro hc
    have hx0 : 0 ≤ x := by
      simpa [cartesianDetourBottom] using hc.1
    have him : 4 * ρ / 5 ≤ m * x := by
      have hfour : 0 ≤ 4 * ρ / 5 := by positivity
      simpa [cartesianDetourBottom, abs_of_nonneg hfour] using hc.2
    by_cases hxz : x = 0
    · subst x
      norm_num at him
      linarith
    · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxz)
      have hmx : m * x < (4 / 3 : ℝ) * x :=
        mul_lt_mul_of_pos_right hm hxpos
      nlinarith [hx.2]

/-- Every point of the left segment is in the genuine Cartesian dent. -/
theorem cartesianDetourLeft_mem {η m ρ y : ℝ}
    (hρ : 0 < ρ) (hρη : 2 * ρ < η)
    (hy : y ∈ Icc (-(4 * ρ / 5)) (4 * ρ / 5)) :
    cartesianDetourLeft ρ y ∈ cartesianDelta η m := by
  have hdist := cartesianDetourLeft_dist_le hρ.le hy
  constructor
  · have htri : ‖cartesianDetourLeft ρ y‖ ≤
        ‖cartesianDetourLeft ρ y - 1‖ + 1 := by
      calc
        ‖cartesianDetourLeft ρ y‖ =
            ‖(cartesianDetourLeft ρ y - 1) + 1‖ := by congr 1; ring
        _ ≤ _ := by simpa only [norm_one] using
          norm_add_le (cartesianDetourLeft ρ y - 1) (1 : ℂ)
    linarith
  · intro hc
    have : (0 : ℝ) ≤ -ρ := by
      simpa [cartesianDetourLeft] using hc.1
    linarith

/-- The Cauchy denominator is uniformly bounded throughout the whole
`1/(2n)`-neighborhood of the singular point, not only on its boundary. -/
theorem near_one_inverse_pow_bound {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ‖z - 1‖ ≤ 1 / (2 * (n : ℝ))) :
    ‖z⁻¹ ^ (n + 1)‖ ≤ Real.exp 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let r : ℝ := 1 / (2 * (n : ℝ))
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    dsimp [r]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hnorm : 1 - r ≤ ‖z‖ := by
    have h := norm_add_le z (1 - z)
    have heq : z + (1 - z) = (1 : ℂ) := by ring
    rw [heq, norm_one, norm_sub_rev] at h
    dsimp [r]
    linarith
  have hbase : 0 < 1 - r := by linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hbase hnorm
  have hloginv : -Real.log (1 - r) ≤ r / (1 - r) := by
    rw [← Real.log_inv]
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hbase)
    (convert h using 1; field_simp; ring)
  have hloglower : -(2 * r) ≤ Real.log ‖z‖ := by
    have hdiv : r / (1 - r) ≤ 2 * r := by
      apply (div_le_iff₀ hbase).2
      nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr hrhalf)]
    have hlog := Real.log_le_log hbase hnorm
    linarith
  have hpow : ‖z⁻¹ ^ (n + 1)‖ = ‖z‖ ^ (-((n : ℝ) + 1)) := by
    calc
      ‖z⁻¹ ^ (n + 1)‖ = (‖z‖⁻¹) ^ (n + 1) := by simp
      _ = (‖z‖ ^ (n + 1 : ℕ))⁻¹ := by rw [inv_pow]
      _ = ‖z‖ ^ (-((n : ℝ) + 1)) := by
        rw [Real.rpow_neg hzpos.le]
        norm_cast
  rw [hpow, Real.rpow_def_of_pos hzpos]
  apply Real.exp_le_exp.mpr
  have hscale : r * ((n : ℝ) + 1) ≤ 1 := by
    dsimp [r]
    calc
      1 / (2 * (n : ℝ)) * ((n : ℝ) + 1) =
          ((n : ℝ) + 1) / (2 * (n : ℝ)) := by ring
      _ ≤ 1 := by
        apply (div_le_iff₀ (mul_pos (by norm_num) hn')).2
        nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  nlinarith [mul_nonneg (add_nonneg (Nat.cast_nonneg n) zero_le_one)
    (sub_nonneg.mpr hloglower)]

/-- The oriented Banach-valued Cauchy integral on the three admissible
segments.  Its endpoints are the two `(3±4i)/5` ray points at distance `ρ`
from `1`. -/
def banachCartesianDetour (F : ℂ → E) (n : ℕ) : E :=
  let ρ := cartesianDetourRadius n
  (-(∫ x in (-ρ)..(3 * ρ / 5),
        (cartesianDetourTop ρ x)⁻¹ ^ (n + 1) • F (cartesianDetourTop ρ x)) -
      Complex.I • (∫ y in (-(4 * ρ / 5))..(4 * ρ / 5),
        (cartesianDetourLeft ρ y)⁻¹ ^ (n + 1) • F (cartesianDetourLeft ρ y)) +
      (∫ x in (-ρ)..(3 * ρ / 5),
        (cartesianDetourBottom ρ x)⁻¹ ^ (n + 1) • F (cartesianDetourBottom ρ x)))

/-- The admissible polygonal detour has exactly the local transfer scale.
Unlike the full small circle, every value of `F` used here lies in
`cartesianDelta`. -/
theorem banachCartesianDetour_bound
    {F : ℂ → E} {η m C a : ℝ} {n : ℕ}
    (hm : m < 4 / 3) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hn : 0 < n) (hη : 1 / (n : ℝ) < η)
    (hF : ∀ z ∈ cartesianDelta η m,
      ‖F z‖ ≤ C * ‖z - 1‖ ^ a) :
    ‖banachCartesianDetour F n‖ ≤
      6 * cartesianDetourRadius n *
        (Real.exp 2 * (C * (2 * cartesianDetourRadius n) ^ a)) := by
  let ρ := cartesianDetourRadius n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ : 0 < ρ := by dsimp [ρ, cartesianDetourRadius]; positivity
  have hρη : 2 * ρ < η := by
    dsimp [ρ, cartesianDetourRadius]
    have hhalf : 2 * (1 / (4 * (n : ℝ))) = 1 / (2 * (n : ℝ)) := by ring
    rw [hhalf]
    have hinv : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn'
    have heq : 1 / (2 * (n : ℝ)) = (1 / (n : ℝ)) / 2 := by ring
    rw [heq]
    linarith
  have hρn : 2 * ρ = 1 / (2 * (n : ℝ)) := by
    dsimp [ρ, cartesianDetourRadius]
    ring
  have hpow (z : ℂ) (hzmem : z ∈ cartesianDelta η m)
      (hzdist : ‖z - 1‖ ≤ 2 * ρ) :
      ‖z⁻¹ ^ (n + 1) • F z‖ ≤ Real.exp 2 * (C * (2 * ρ) ^ a) := by
    rw [norm_smul]
    have hden : ‖z⁻¹ ^ (n + 1)‖ ≤ Real.exp 2 :=
      near_one_inverse_pow_bound hn (by simpa only [hρn] using hzdist)
    have hdistpow : ‖z - 1‖ ^ a ≤ (2 * ρ) ^ a :=
      Real.rpow_le_rpow (norm_nonneg _) hzdist ha
    have hFz : ‖F z‖ ≤ C * (2 * ρ) ^ a :=
      (hF z hzmem).trans (mul_le_mul_of_nonneg_left hdistpow hC)
    exact (mul_le_mul hden hFz (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)
  let B : ℝ := Real.exp 2 * (C * (2 * ρ) ^ a)
  have htop : ‖∫ x in (-ρ)..(3 * ρ / 5),
      (cartesianDetourTop ρ x)⁻¹ ^ (n + 1) • F (cartesianDetourTop ρ x)‖ ≤
      (8 * ρ / 5) * B := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ =>
        (cartesianDetourTop ρ x)⁻¹ ^ (n + 1) • F (cartesianDetourTop ρ x))
      (C := B) (fun x hx => by
        have hu : uIoc (-ρ) (3 * ρ / 5) = Ioc (-ρ) (3 * ρ / 5) :=
          uIoc_of_le (by linarith)
        have hxIoc : x ∈ Ioc (-ρ) (3 * ρ / 5) := hu ▸ hx
        have hx' : x ∈ Icc (-ρ) (3 * ρ / 5) :=
          Ioc_subset_Icc_self hxIoc
        exact hpow _ (cartesianDetourTop_mem hm hρ hρη hx')
          (cartesianDetourTop_dist_le hρ.le hx'))
    rw [abs_of_nonneg (by linarith : 0 ≤ 3 * ρ / 5 - (-ρ))] at hb
    (convert hb using 1; dsimp [B]; ring)
  have hbottom : ‖∫ x in (-ρ)..(3 * ρ / 5),
      (cartesianDetourBottom ρ x)⁻¹ ^ (n + 1) • F (cartesianDetourBottom ρ x)‖ ≤
      (8 * ρ / 5) * B := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ =>
        (cartesianDetourBottom ρ x)⁻¹ ^ (n + 1) • F (cartesianDetourBottom ρ x))
      (C := B) (fun x hx => by
        have hu : uIoc (-ρ) (3 * ρ / 5) = Ioc (-ρ) (3 * ρ / 5) :=
          uIoc_of_le (by linarith)
        have hxIoc : x ∈ Ioc (-ρ) (3 * ρ / 5) := hu ▸ hx
        have hx' : x ∈ Icc (-ρ) (3 * ρ / 5) :=
          Ioc_subset_Icc_self hxIoc
        exact hpow _ (cartesianDetourBottom_mem hm hρ hρη hx')
          (cartesianDetourBottom_dist_le hρ.le hx'))
    rw [abs_of_nonneg (by linarith : 0 ≤ 3 * ρ / 5 - (-ρ))] at hb
    (convert hb using 1; dsimp [B]; ring)
  have hleft : ‖Complex.I • (∫ y in (-(4 * ρ / 5))..(4 * ρ / 5),
      (cartesianDetourLeft ρ y)⁻¹ ^ (n + 1) • F (cartesianDetourLeft ρ y))‖ ≤
      (8 * ρ / 5) * B := by
    rw [norm_smul, Complex.norm_I, one_mul]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y : ℝ =>
        (cartesianDetourLeft ρ y)⁻¹ ^ (n + 1) • F (cartesianDetourLeft ρ y))
      (C := B) (fun y hy => by
        have hu : uIoc (-(4 * ρ / 5)) (4 * ρ / 5) =
            Ioc (-(4 * ρ / 5)) (4 * ρ / 5) := uIoc_of_le (by linarith)
        have hyIoc : y ∈ Ioc (-(4 * ρ / 5)) (4 * ρ / 5) := hu ▸ hy
        have hy' : y ∈ Icc (-(4 * ρ / 5)) (4 * ρ / 5) :=
          Ioc_subset_Icc_self hyIoc
        exact hpow _ (cartesianDetourLeft_mem hρ hρη hy')
          (cartesianDetourLeft_dist_le hρ.le hy'))
    rw [abs_of_nonneg (by linarith :
      0 ≤ 4 * ρ / 5 - (-(4 * ρ / 5)))] at hb
    (convert hb using 1; dsimp [B]; ring)
  let T : E := ∫ x in (-ρ)..(3 * ρ / 5),
    (cartesianDetourTop ρ x)⁻¹ ^ (n + 1) • F (cartesianDetourTop ρ x)
  let L : E := Complex.I • (∫ y in (-(4 * ρ / 5))..(4 * ρ / 5),
    (cartesianDetourLeft ρ y)⁻¹ ^ (n + 1) • F (cartesianDetourLeft ρ y))
  let D : E := ∫ x in (-ρ)..(3 * ρ / 5),
    (cartesianDetourBottom ρ x)⁻¹ ^ (n + 1) • F (cartesianDetourBottom ρ x)
  have hT : ‖T‖ ≤ (8 * ρ / 5) * B := htop
  have hL : ‖L‖ ≤ (8 * ρ / 5) * B := hleft
  have hD : ‖D‖ ≤ (8 * ρ / 5) * B := hbottom
  have hfirst : ‖-T - L‖ ≤ ‖T‖ + ‖L‖ := by
    simpa only [norm_neg] using norm_sub_le (-T) L
  have hall : ‖-T - L + D‖ ≤
      (8 * ρ / 5) * B + (8 * ρ / 5) * B + (8 * ρ / 5) * B := by
    calc
      ‖-T - L + D‖ ≤ ‖-T - L‖ + ‖D‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  change ‖-T - L + D‖ ≤ _
  dsimp [ρ, B] at hall ⊢
  exact hall.trans (by
    have hscale : 0 ≤ cartesianDetourRadius n *
        (Real.exp 2 * (C * (2 * cartesianDetourRadius n) ^ a)) := by
      dsimp [cartesianDetourRadius]
      positivity
    nlinarith)

/-- The elementary scale in the preceding estimate is exactly a constant
multiple of `n^(-a-1)`. -/
theorem cartesianDetour_scale_eq (a : ℝ) {n : ℕ} (hn : 0 < n) :
    cartesianDetourRadius n * (2 * cartesianDetourRadius n) ^ a =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a *
        (n : ℝ) ^ (-(a + 1)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := hnpos.le
  have hρ : cartesianDetourRadius n = (1 / 4 : ℝ) * (n : ℝ)⁻¹ := by
    dsimp [cartesianDetourRadius]
    field_simp
  have h2ρ : 2 * cartesianDetourRadius n =
      (1 / 2 : ℝ) * (n : ℝ)⁻¹ := by
    dsimp [cartesianDetourRadius]
    field_simp
    norm_num
  rw [h2ρ, hρ, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (inv_nonneg.mpr hn0)]
  calc
    (1 / 4 * (n : ℝ)⁻¹) *
        ((1 / 2 : ℝ) ^ a * ((n : ℝ)⁻¹) ^ a) =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a *
        ((n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-a)) := by
          rw [Real.rpow_neg_one, Real.rpow_neg_eq_inv_rpow]
          ring
    _ = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a *
        (n : ℝ) ^ ((-1 : ℝ) + (-a)) := by
          rw [Real.rpow_add hnpos]
    _ = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a *
        (n : ℝ) ^ (-(a + 1)) := by ring_nf

/-- The admissible local detour is a genuine Banach-valued
`O(n^(-a-1))` contribution, derived from the Cartesian Δ-bound alone. -/
theorem banachCartesianDetour_isBigO
    {F : ℂ → E} {η m C a : ℝ}
    (hη : 0 < η) (hm : m < 4 / 3) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hF : ∀ z ∈ cartesianDelta η m,
      ‖F z‖ ≤ C * ‖z - 1‖ ^ a) :
    (fun n : ℕ => banachCartesianDetour F n) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(a + 1))) := by
  let K : ℝ := 6 * Real.exp 2 * C *
    ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  rw [Asymptotics.isBigO_iff]
  refine ⟨K, ?_⟩
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n : ℝ) < η := by
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds hη)
    simpa only [one_div] using ht
  filter_upwards [hsmall, Filter.eventually_ge_atTop (1 : ℕ)] with n hnη hn
  have hnpos : 0 < n := by omega
  have hb := banachCartesianDetour_bound hm hC ha hnpos hnη hF
  have htarget : 0 ≤ (n : ℝ) ^ (-(a + 1)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_eq_abs, abs_of_nonneg htarget]
  calc
    ‖banachCartesianDetour F n‖ ≤
        6 * cartesianDetourRadius n *
          (Real.exp 2 * (C * (2 * cartesianDetourRadius n) ^ a)) := hb
    _ = (6 * Real.exp 2 * C) *
        (cartesianDetourRadius n *
          (2 * cartesianDetourRadius n) ^ a) := by ring
    _ = (6 * Real.exp 2 * C) *
        ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a *
          (n : ℝ) ^ (-(a + 1))) := by
            rw [cartesianDetour_scale_eq a hnpos]
    _ = K * (n : ℝ) ^ (-(a + 1)) := by
      dsimp [K]
      ring

/-- The complete *local* keyhole: the upper ray is traversed towards the
singularity, the admissible polygonal detour joins its endpoint to the lower
ray, and the lower ray is traversed outwards.  Every value of `F` occurring
here is on the two Cartesian-Delta rays or on the polygon proved admissible
above. -/
def banachCartesianLocalKeyhole (F : ℂ → E) (M : ℝ) (n : ℕ) : E :=
  let ρ := cartesianDetourRadius n
  (-(∫ t in ρ..M,
        (cartesianUpperDir *
          (((1 : ℂ) + (t : ℂ) * cartesianUpperDir)⁻¹ ^ (n + 1))) •
            F ((1 : ℂ) + (t : ℂ) * cartesianUpperDir)) +
    banachCartesianDetour F n +
    (∫ t in ρ..M,
        (cartesianLowerDir *
          (((1 : ℂ) + (t : ℂ) * cartesianLowerDir)⁻¹ ^ (n + 1))) •
            F ((1 : ℂ) + (t : ℂ) * cartesianLowerDir)))

/-- A fully internal estimate for the actual local keyhole in the Cartesian
dent.  In particular, neither ray membership nor an inner-contour hypothesis
is exposed as an interface. -/
theorem banachCartesianLocalKeyhole_bound
    {F : ℂ → E} {M a η m : ℝ} {n : ℕ}
    (hM1 : M ≤ 1) (hMη : M < η)
    (hm : m < 4 / 3) (ha : 0 ≤ a) (hn : 0 < n)
    (hρM : cartesianDetourRadius n ≤ M)
    (hη : 1 / (n : ℝ) < η)
    (hF : ∀ z ∈ cartesianDelta η m,
      ‖F z‖ ≤ ‖z - 1‖ ^ a) :
    ‖banachCartesianLocalKeyhole F M n‖ ≤
      2 * ((1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1)) +
        6 * cartesianDetourRadius n *
          (Real.exp 2 * (2 * cartesianDetourRadius n) ^ a) := by
  let ρ := cartesianDetourRadius n
  let U : E := ∫ t in ρ..M,
    (cartesianUpperDir *
      (((1 : ℂ) + (t : ℂ) * cartesianUpperDir)⁻¹ ^ (n + 1))) •
        F ((1 : ℂ) + (t : ℂ) * cartesianUpperDir)
  let L : E := ∫ t in ρ..M,
    (cartesianLowerDir *
      (((1 : ℂ) + (t : ℂ) * cartesianLowerDir)⁻¹ ^ (n + 1))) •
        F ((1 : ℂ) + (t : ℂ) * cartesianLowerDir)
  let D : E := banachCartesianDetour F n
  have hρ : 0 ≤ ρ := by
    dsimp [ρ, cartesianDetourRadius]
    positivity
  have ha' : -1 < a := by linarith
  have hU : ‖U‖ ≤
      (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) := by
    exact banach_radial_piece_from_on_cartesianDelta
      norm_cartesianUpperDir cartesianUpperDir_re
      cartesianUpperDir_abs_im hρ hρM hM1 hMη hm ha' hn hF
  have hL : ‖L‖ ≤
      (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) := by
    exact banach_radial_piece_from_on_cartesianDelta
      norm_cartesianLowerDir cartesianLowerDir_re
      cartesianLowerDir_abs_im hρ hρM hM1 hMη hm ha' hn hF
  have hD : ‖D‖ ≤ 6 * ρ * (Real.exp 2 * (2 * ρ) ^ a) := by
    simpa only [one_mul] using
      (banachCartesianDetour_bound hm (by norm_num : (0 : ℝ) ≤ 1)
        ha hn hη (by simpa only [one_mul] using hF))
  change ‖-U + D + L‖ ≤ _
  have hsum : ‖-U + D + L‖ ≤ ‖U‖ + ‖D‖ + ‖L‖ := by
    calc
      ‖-U + D + L‖ ≤ ‖-U + D‖ + ‖L‖ := norm_add_le _ _
      _ ≤ (‖U‖ + ‖D‖) + ‖L‖ := by
        gcongr
        simpa only [norm_neg] using norm_add_le (-U) D
  dsimp [ρ] at hD ⊢
  linarith

/-- The Laplace scale appearing on either ray is exactly a constant
multiple of `n^(-a-1)`. -/
theorem cartesianRay_scale_eq (a : ℝ) {n : ℕ} (hn : 0 < n) :
    (1 / ((1 / 4 : ℝ) * (n : ℝ))) ^ (a + 1) =
      (4 : ℝ) ^ (a + 1) * (n : ℝ) ^ (-(a + 1)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := hnpos.le
  have hbase : 1 / ((1 / 4 : ℝ) * (n : ℝ)) =
      4 * (n : ℝ)⁻¹ := by
    field_simp
  rw [hbase, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
    (inv_nonneg.mpr hn0), ← Real.rpow_neg_eq_inv_rpow]

/-- The complete admissible local keyhole is a genuine Banach-valued
`O(n^(-a-1))` term under the Cartesian-Delta power bound alone. -/
theorem banachCartesianLocalKeyhole_isBigO
    {F : ℂ → E} {M a η m : ℝ}
    (hM : 0 < M) (hM1 : M ≤ 1) (hMη : M < η)
    (hm : m < 4 / 3) (ha : 0 ≤ a)
    (hF : ∀ z ∈ cartesianDelta η m,
      ‖F z‖ ≤ ‖z - 1‖ ^ a) :
    (fun n : ℕ => banachCartesianLocalKeyhole F M n) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(a + 1))) := by
  let K : ℝ :=
    2 * ((4 : ℝ) ^ (a + 1) * Gamma (a + 1)) +
      6 * Real.exp 2 * ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a)
  have hK : 0 ≤ K := by
    have hapos : 0 < a + 1 := by linarith
    dsimp [K]
    positivity
  rw [Asymptotics.isBigO_iff]
  refine ⟨K, ?_⟩
  have hsmallM : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n : ℝ) < M := by
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds hM)
    simpa only [one_div] using ht
  have hη : 0 < η := hM.trans hMη
  have hsmallη : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n : ℝ) < η := by
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds hη)
    simpa only [one_div] using ht
  filter_upwards [hsmallM, hsmallη,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hnM hnη hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hρinv : cartesianDetourRadius n ≤ 1 / (n : ℝ) := by
    calc
      cartesianDetourRadius n =
          (1 / 4 : ℝ) * (1 / (n : ℝ)) := by
            dsimp [cartesianDetourRadius]
            field_simp
      _ ≤ 1 / (n : ℝ) := by
        nlinarith [one_div_pos.mpr hnreal]
  have hρM : cartesianDetourRadius n ≤ M := hρinv.trans hnM.le
  have hb := banachCartesianLocalKeyhole_bound
    hM1 hMη hm ha hnpos hρM hnη hF
  have htarget : 0 ≤ (n : ℝ) ^ (-(a + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_eq_abs, abs_of_nonneg htarget]
  calc
    ‖banachCartesianLocalKeyhole F M n‖ ≤
        2 * ((1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1)) +
          6 * cartesianDetourRadius n *
            (Real.exp 2 * (2 * cartesianDetourRadius n) ^ a) := hb
    _ = 2 * (((4 : ℝ) ^ (a + 1) *
          (n : ℝ) ^ (-(a + 1))) * Gamma (a + 1)) +
        6 * Real.exp 2 *
          ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a *
            (n : ℝ) ^ (-(a + 1))) := by
          rw [cartesianRay_scale_eq a hnpos]
          calc
            2 * (4 ^ (a + 1) * (n : ℝ) ^ (-(a + 1)) *
                Gamma (a + 1)) +
                6 * cartesianDetourRadius n *
                  (Real.exp 2 * (2 * cartesianDetourRadius n) ^ a) =
              2 * (4 ^ (a + 1) * (n : ℝ) ^ (-(a + 1)) *
                Gamma (a + 1)) +
                6 * Real.exp 2 *
                  (cartesianDetourRadius n *
                    (2 * cartesianDetourRadius n) ^ a) := by ring
            _ = _ := by rw [cartesianDetour_scale_eq a hnpos]
    _ = K * (n : ℝ) ^ (-(a + 1)) := by
      dsimp [K]
      ring

end PerronWright.Transfer
