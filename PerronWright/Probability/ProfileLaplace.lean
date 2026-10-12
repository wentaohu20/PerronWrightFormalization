import PerronWright.Probability.ProfileEnumeration
import PerronWright.Probability.ConnectedTypeDomination
import PerronWright.Probability.ConnectedTypeTails

/-!
# Uniform centered profile logarithmic Laplace bounds

The exact transform of the literal connected type law is combined with
the actual analytic log-radius and complete general-field enumeration.
No field-transfer, concentration, or radius-Taylor interface is assumed.
-/

open MeasureTheory Filter Topology
open scoped Topology Real

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.ProfileLaplace

open FieldLogRadiusTaylor ConnectedTypeLaw

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal connected enumerator with its true critical-radius factor. -/
def normalizedWeight (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℝ)) (k r : ℕ) : ℝ :=
  realRadius M hM g ^ k * M.fieldConnectedWeight g k r

/-- Exact logarithmic transform decomposition into the radius response
and a normalized connected-enumerator ratio. -/
theorem centered_logLaplace_eq (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g f : C(S, ℝ)) (k r : ℕ) (hC : 0 < M.fieldConnectedWeight g k r)
    (hg : 0 < realRadius M hM g) (hgf : 0 < realRadius M hM (g + f)) :
    Real.log (∫ p, Real.exp (typeSum f p.1 -
        (k : ℝ) * ∫ x, f x ∂M.perronLaw hM) ∂law M g k r hC) =
      -(k : ℝ) * ((∫ x, f x ∂M.perronLaw hM) +
        realLogRadius M hM (g + f) - realLogRadius M hM g) +
      Real.log (normalizedWeight M hM (g + f) k r /
        normalizedWeight M hM g k r) := by
  have hCf : 0 < M.fieldConnectedWeight (g + f) k r :=
    (normalizer_pos_iff_zero_field M (g + f) k r).mpr
      ((normalizer_pos_iff_zero_field M g k r).mp hC)
  rw [centered_laplace_eq_enumerator_ratio,
    Real.log_mul (Real.exp_ne_zero _) (div_pos hCf hC).ne', Real.log_exp,
    Real.log_div hCf.ne' hC.ne']
  unfold normalizedWeight realLogRadius
  rw [Real.log_div (mul_pos (pow_pos hgf _) hCf).ne'
      (mul_pos (pow_pos hg _) hC).ne',
    Real.log_mul (pow_ne_zero _ hgf.ne') hCf.ne',
    Real.log_mul (pow_ne_zero _ hg.ne') hC.ne', Real.log_pow, Real.log_pow]
  ring

/-- On one small actual field ball, the radius-normalized real connected
weight ratio is bounded by three, uniformly for bounded surplus. -/
theorem exists_normalizedWeight_ratio_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ g h : C(S, ℝ), ‖g‖ ≤ ε → ‖h‖ ≤ ε →
        |normalizedWeight M hM g k r / normalizedWeight M hM h k r| ≤ 3 := by
  obtain ⟨ε₁, hε₁, henum⟩ :=
    ProfileEnumeration.exists_boundedSurplus_normalized_ratio_bound M hM R
  obtain ⟨ε₂, hε₂, hreal⟩ := exists_realRadius_positive_branch M hM
  let ε : ℝ := min ε₁ (ε₂ / 2)
  have hε : 0 < ε := lt_min hε₁ (by positivity)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [henum] with k hk
  intro r hr g h hg hh
  have hε₂lt : ε < ε₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hgr := (hreal g (hg.trans_lt hε₂lt)).2.1
  have hhr := (hreal h (hh.trans_lt hε₂lt)).2.1
  have he := hk r hr (CompactBJRModel.complexifyField g)
    (CompactBJRModel.complexifyField h)
    (by simpa only [norm_complexifyField] using hg.trans (min_le_left _ _))
    (by simpa only [norm_complexifyField] using hh.trans (min_le_left _ _))
  rw [hgr, hhr, M.complexFieldConnectedWeight_complexifyField,
    M.complexFieldConnectedWeight_complexifyField] at he
  simpa only [normalizedWeight, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs] using he

/-- Section 5's genuine single-component source-field log-Laplace bound.
The constants and the size threshold are chosen uniformly before `r`,
`g`, and `f`. The additive `log 3` is the normalized-enumerator correction. -/
theorem exists_centered_logLaplace_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R →
        (∀ g : C(S, ℝ), 0 < M.fieldConnectedWeight g k r) ∧
        ∀ g f : C(S, ℝ), ‖g‖ + ‖f‖ < ε →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
          Real.log (∫ p, Real.exp (typeSum f p.1 -
              (k : ℝ) * ∫ x, f x ∂M.perronLaw hM) ∂law M g k r hC) ≤
            C * (k : ℝ) * (‖f‖ ^ 2 + ‖g‖ * ‖f‖) + Real.log 3 := by
  obtain ⟨ε₁, C, hε₁, hC, htaylor⟩ := exists_realLogRadius_increment_bound M hM
  obtain ⟨ε₂, hε₂, hratio⟩ := exists_normalizedWeight_ratio_bound M hM R
  obtain ⟨ε₃, hε₃, hreal⟩ := exists_realRadius_positive_branch M hM
  let ε : ℝ := min ε₁ (min ε₂ ε₃)
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₃)
  refine ⟨ε, C, hε, hC, ?_⟩
  filter_upwards [hratio, eventually_all_field_normalizers_pos M hM R] with k hk hpos
  intro r hr
  refine ⟨hpos r hr, ?_⟩
  intro g f hgf hCg
  have hsum : ‖g + f‖ < ε := (norm_add_le g f).trans_lt hgf
  have hg : ‖g‖ < ε := by linarith [norm_nonneg f]
  have hε₂ : ε ≤ ε₂ := (min_le_right ε₁ _).trans (min_le_left _ _)
  have hε₃ : ε ≤ ε₃ := (min_le_right ε₁ _).trans (min_le_right _ _)
  have hrg := (hreal g (hg.trans_le hε₃)).1
  have hrgf := (hreal (g + f) (hsum.trans_le hε₃)).1
  have hnormg : 0 < normalizedWeight M hM g k r :=
    mul_pos (pow_pos hrg _) hCg
  have hnormgf : 0 < normalizedWeight M hM (g + f) k r :=
    mul_pos (pow_pos hrgf _) (hpos r hr (g + f))
  have hquot : 0 < normalizedWeight M hM (g + f) k r / normalizedWeight M hM g k r :=
    div_pos hnormgf hnormg
  have hquotBound := hk r hr (g + f) g (hsum.trans_le hε₂).le (hg.trans_le hε₂).le
  rw [abs_of_pos hquot] at hquotBound
  have hlogBound : Real.log (normalizedWeight M hM (g + f) k r /
      normalizedWeight M hM g k r) ≤ Real.log 3 :=
    (Real.log_le_log_iff hquot (by norm_num)).mpr hquotBound
  have ht := htaylor g f (hgf.trans_le (min_le_left _ _))
  have hrad : -(k : ℝ) * ((∫ x, f x ∂M.perronLaw hM) +
      realLogRadius M hM (g + f) - realLogRadius M hM g) ≤
      C * (k : ℝ) * (‖f‖ ^ 2 + ‖g‖ * ‖f‖) := by
    have hlo := (neg_le_abs (realLogRadius M hM (g + f) -
      realLogRadius M hM g + ∫ x, f x ∂M.perronLaw hM)).trans
        ht
    have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg k)
    nlinarith only [hm]
  rw [centered_logLaplace_eq M hM g f k r hCg hrg hrgf]
  exact add_le_add hrad hlogBound

/-- The same proven bound in the exponential form used by Chernoff.
The law's positivity is supplied by genuine enumeration in the conclusion. -/
theorem exists_centered_Laplace_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R →
        (∀ g : C(S, ℝ), 0 < M.fieldConnectedWeight g k r) ∧
        ∀ g f : C(S, ℝ), ‖g‖ + ‖f‖ < ε →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
          (∫ p, Real.exp (typeSum f p.1 -
              (k : ℝ) * ∫ x, f x ∂M.perronLaw hM) ∂law M g k r hC) ≤
            Real.exp (C * (k : ℝ) * (‖f‖ ^ 2 + ‖g‖ * ‖f‖) + Real.log 3) := by
  obtain ⟨ε, C, hε, hC, hbound⟩ := exists_centered_logLaplace_bound M hM R
  refine ⟨ε, C, hε, hC, ?_⟩
  filter_upwards [hbound] with k hk
  intro r hr
  refine ⟨(hk r hr).1, ?_⟩
  intro g f hgf hCg
  have hepos : 0 < (∫ p, Real.exp (typeSum f p.1 -
      (k : ℝ) * ∫ x, f x ∂M.perronLaw hM) ∂law M g k r hCg) := by
    rw [centered_laplace_eq_enumerator_ratio]
    exact mul_pos (Real.exp_pos _) (div_pos ((hk r hr).1 (g + f)) hCg)
  have he := Real.exp_le_exp.mpr ((hk r hr).2 g f hgf hCg)
  rwa [Real.exp_log hepos] at he

/-- The centered, unnormalized empirical type statistic. -/
def centeredSum (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (f : C(S, ℝ)) (p : State S k) : ℝ :=
  typeSum f p.1 - (k : ℝ) * ∫ x, f x ∂M.perronLaw hM

theorem centeredSum_smul (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (f : C(S, ℝ)) (s : ℝ) (p : State S k) :
    centeredSum M hM (s • f) p = s * centeredSum M hM f p := by
  simp only [centeredSum, typeSum_smul, ContinuousMap.smul_apply, smul_eq_mul,
    integral_const_mul]
  ring

theorem integrable_exp_centeredSum (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (g f : C(S, ℝ)) (k r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) :
    Integrable (fun p : State S k ↦ Real.exp (centeredSum M hM f p))
      (law M g k r hC) := by
  simp only [centeredSum, Real.exp_sub]
  exact (integrable_exp_typeSum M g f k r hC).div_const _

/-- A literal one-component centered probability-tail bound, with one
common field domain and constants for all `r ≤ R`. -/
theorem exists_centered_upper_tail_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R →
        (∀ g : C(S, ℝ), 0 < M.fieldConnectedWeight g k r) ∧
        ∀ g f : C(S, ℝ), ∀ s z : ℝ, 0 ≤ s → ‖g‖ + s * ‖f‖ < ε →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
          (law M g k r hC).real {p | z ≤ centeredSum M hM f p} ≤
            Real.exp (-s * z + C * (k : ℝ) *
              ((s * ‖f‖) ^ 2 + ‖g‖ * (s * ‖f‖)) + Real.log 3) := by
  obtain ⟨ε, C, hε, hC, hbound⟩ := exists_centered_Laplace_bound M hM R
  refine ⟨ε, C, hε, hC, ?_⟩
  filter_upwards [hbound] with k hk
  intro r hr
  refine ⟨(hk r hr).1, ?_⟩
  intro g f s z hs hgf hCg
  have hsnorm : ‖s • f‖ = s * ‖f‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hi : Integrable (fun p : State S k ↦ Real.exp (s * centeredSum M hM f p))
      (law M g k r hCg) := by
    simpa only [centeredSum_smul] using integrable_exp_centeredSum M hM g (s • f) k r hCg
  have hm := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := centeredSum M hM f) (μ := law M g k r hCg) z hs hi
  have hmgf : ProbabilityTheory.mgf (centeredSum M hM f) (law M g k r hCg) s ≤
      Real.exp (C * (k : ℝ) * ((s * ‖f‖) ^ 2 + ‖g‖ * (s * ‖f‖)) + Real.log 3) := by
    have hb := (hk r hr).2 g (s • f) (by rwa [hsnorm]) hCg
    change (∫ p, Real.exp (centeredSum M hM (s • f) p) ∂law M g k r hCg) ≤ _ at hb
    simpa only [ProbabilityTheory.mgf, centeredSum_smul, hsnorm] using hb
  refine hm.trans ((mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le).trans_eq ?_)
  rw [← Real.exp_add]
  congr 1
  ring

/-- Optimized Gaussian upper tail for every unit-norm continuous test
field, uniform for bounded surplus. The allowed deviation grows linearly
with the component size; a nonzero enumerating field gives the explicit
linear drift correction. -/
theorem exists_centered_gaussian_upper_tail_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      0 < k ∧ ∀ r : ℕ, r ≤ R →
        (∀ g : C(S, ℝ), 0 < M.fieldConnectedWeight g k r) ∧
        ∀ g f : C(S, ℝ), ‖f‖ ≤ 1 → ∀ z : ℝ, 0 ≤ z →
          ‖g‖ + z / (2 * C * (k : ℝ)) < ε →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
          (law M g k r hC).real {p | z ≤ centeredSum M hM f p} ≤
            Real.exp (-z ^ 2 / (4 * C * (k : ℝ)) + ‖g‖ * z / 2 + Real.log 3) := by
  obtain ⟨ε, C, hε, hC, hbound⟩ := exists_centered_upper_tail_bound M hM R
  refine ⟨ε, C, hε, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with k hk hk1
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hk1
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  refine ⟨hkpos, ?_⟩
  intro r hr
  refine ⟨(hk r hr).1, ?_⟩
  intro g f hf z hz hwindow hCg
  let s : ℝ := z / (2 * C * (k : ℝ))
  have hs : 0 ≤ s := div_nonneg hz (by positivity)
  have hsnorm : s * ‖f‖ ≤ s := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf hs
  have hsfield : ‖g‖ + s * ‖f‖ < ε :=
    by change ‖g‖ + s < ε at hwindow; linarith only [hsnorm, hwindow]
  have he := (hk r hr).2 g f s z hs hsfield hCg
  refine he.trans (Real.exp_le_exp.mpr ?_)
  have hsq : (s * ‖f‖) ^ 2 ≤ s ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hs (norm_nonneg f)) hsnorm 2
  have hlin : ‖g‖ * (s * ‖f‖) ≤ ‖g‖ * s :=
    mul_le_mul_of_nonneg_left hsnorm (norm_nonneg g)
  have hmono := mul_le_mul_of_nonneg_left (add_le_add hsq hlin)
    (mul_pos hC hkreal).le
  calc
    -s * z + C * (k : ℝ) * ((s * ‖f‖) ^ 2 + ‖g‖ * (s * ‖f‖)) + Real.log 3 ≤
      -s * z + C * (k : ℝ) * (s ^ 2 + ‖g‖ * s) + Real.log 3 := by linarith
    _ = -z ^ 2 / (4 * C * (k : ℝ)) + ‖g‖ * z / 2 + Real.log 3 := by
      dsimp only [s]
      field_simp [hC.ne', hkreal.ne']
      ring

theorem centeredSum_neg (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (f : C(S, ℝ)) (p : State S k) :
    centeredSum M hM (-f) p = -centeredSum M hM f p := by
  simpa only [neg_one_smul, neg_one_mul] using centeredSum_smul M hM f (-1) p

/-- Two-sided Gaussian connected-profile concentration, derived for the
actual probability law from the actual analytic field enumeration. -/
theorem exists_centered_gaussian_tail_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      0 < k ∧ ∀ r : ℕ, r ≤ R →
        (∀ g : C(S, ℝ), 0 < M.fieldConnectedWeight g k r) ∧
        ∀ g f : C(S, ℝ), ‖f‖ ≤ 1 → ∀ z : ℝ, 0 ≤ z →
          ‖g‖ + z / (2 * C * (k : ℝ)) < ε →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
          (law M g k r hC).real {p | z ≤ |centeredSum M hM f p|} ≤
            2 * Real.exp (-z ^ 2 / (4 * C * (k : ℝ)) + ‖g‖ * z / 2 + Real.log 3) := by
  obtain ⟨ε, C, hε, hC, hbound⟩ := exists_centered_gaussian_upper_tail_bound M hM R
  refine ⟨ε, C, hε, hC, ?_⟩
  filter_upwards [hbound] with k hk
  refine ⟨hk.1, ?_⟩
  intro r hr
  refine ⟨(hk.2 r hr).1, ?_⟩
  intro g f hf z hz hwindow hCg
  have hp := (hk.2 r hr).2 g f hf z hz hwindow hCg
  have hn := (hk.2 r hr).2 g (-f) (by simpa only [norm_neg] using hf) z hz hwindow hCg
  have hsets : {p : State S k | z ≤ |centeredSum M hM f p|} =
      {p | z ≤ centeredSum M hM f p} ∪ {p | z ≤ centeredSum M hM (-f) p} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, centeredSum_neg]
    by_cases hsign : 0 ≤ centeredSum M hM f p
    · rw [abs_of_nonneg hsign]
      constructor
      · exact Or.inl
      · rintro (h | h) <;> linarith
    · rw [abs_of_neg (lt_of_not_ge hsign)]
      constructor
      · exact Or.inr
      · rintro (h | h) <;> linarith
  rw [hsets]
  exact (measureReal_union_le _ _).trans (by linarith)

/-- The critical-window profile tail on the natural square-root scale.
The deviation range `x ≤ η sqrt k` expands with the component size.
All constants and thresholds are uniform in `r ≤ R`, the test field, and
the current source field satisfying `sqrt k * ‖g‖ ≤ L`. -/
theorem exists_criticalWindow_gaussian_tail_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L : ℝ) (_hL : 0 ≤ L) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      0 < k ∧ ∀ r : ℕ, r ≤ R →
        (∀ g : C(S, ℝ), 0 < M.fieldConnectedWeight g k r) ∧
        ∀ g f : C(S, ℝ), Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ‖f‖ ≤ 1 →
          ∀ x : ℝ, 0 ≤ x → x ≤ η * Real.sqrt (k : ℝ) →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
          (law M g k r hC).real
              {p | x * Real.sqrt (k : ℝ) ≤ |centeredSum M hM f p|} ≤
            2 * Real.exp (-x ^ 2 / (4 * C) + L * x / 2 + Real.log 3) := by
  obtain ⟨ε, C, hε, hC, hbound⟩ := exists_centered_gaussian_tail_bound M hM R
  let η : ℝ := C * ε / 2
  have hη : 0 < η := by dsimp only [η]; positivity
  have hsmall : Tendsto (fun k : ℕ ↦ L * (k : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop)
  refine ⟨η, C, hη, hC, ?_⟩
  filter_upwards [hbound, hsmall.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2))]
    with k hk hksmall
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hsqrtSq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hkreal.le
  have hhalf : (k : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (k : ℝ))⁻¹ := by
    rw [Real.rpow_neg hkreal.le, ← Real.sqrt_eq_rpow]
  refine ⟨hk.1, ?_⟩
  intro r hr
  refine ⟨(hk.2 r hr).1, ?_⟩
  intro g f hg hf x hx hxrange hCg
  have hgnorm : ‖g‖ ≤ L * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hhalf, ← div_eq_mul_inv]
    apply (le_div_iff₀ hsqrt).mpr
    nlinarith only [hg]
  have hgsmall : ‖g‖ < ε / 2 := hgnorm.trans_lt hksmall
  have hfracEq : x * Real.sqrt (k : ℝ) / (2 * C * (k : ℝ)) =
      x / (2 * C * Real.sqrt (k : ℝ)) := by
    nth_rw 2 [← hsqrtSq]
    field_simp [hC.ne', hsqrt.ne']
  have hfrac : x * Real.sqrt (k : ℝ) / (2 * C * (k : ℝ)) ≤ ε / 4 := by
    rw [hfracEq]
    apply (div_le_iff₀ (by positivity : 0 < 2 * C * Real.sqrt (k : ℝ))).mpr
    dsimp only [η] at hxrange
    nlinarith only [hxrange]
  have hwindow : ‖g‖ + x * Real.sqrt (k : ℝ) / (2 * C * (k : ℝ)) < ε := by
    linarith only [hgsmall, hfrac, hε]
  have he := (hk.2 r hr).2 g f hf (x * Real.sqrt (k : ℝ))
    (mul_nonneg hx hsqrt.le) hwindow hCg
  refine he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  have hquadratic : -(x * Real.sqrt (k : ℝ)) ^ 2 / (4 * C * (k : ℝ)) =
      -x ^ 2 / (4 * C) := by
    rw [mul_pow, hsqrtSq]
    field_simp [hC.ne', hkreal.ne']
  have hlinear : ‖g‖ * (x * Real.sqrt (k : ℝ)) / 2 ≤ L * x / 2 := by
    have hm := mul_le_mul_of_nonneg_right hg hx
    nlinarith only [hm]
  rw [hquadratic]
  linarith only [hlinear]

end PerronWright.ProfileLaplace
