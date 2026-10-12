import PerronWright.Enumeration.PositiveSurplusPerronWrightFormula
import PerronWright.Analysis.RelativeErrorProduct

/-!
# The bounded-surplus Perron--Wright formula

The low-surplus theorem and the actual positive-surplus theorem are combined
by induction on the surplus cutoff.  Thus the common constant and eventual
threshold are extracted from a genuinely finite family; no familywise
asymptotic assertion is assumed.  The radius statement holds on every
nonnegative shrinking window.  The standard square-root window is then
converted to the Gaussian form by the proved scalar-radius expansion.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology BigOperators ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.BoundedSurplusPerronWrightFormula

namespace Main

export PerronWright.PerronWrightFormulaMainTerm
  (wrightConstant wrightConstant_pos
   perronWrightRadiusMainTerm
   exists_lowSurplus_unified_radius_relative_bound_uniform_eta
   exists_lowSurplus_unified_radius_relative_bound_of_tendsto)

end Main

namespace Positive

export PerronWright.PositiveSurplusPerronWrightFormula
  (exists_positiveSurplusPerronWright_radius_relative_bound_uniform_eta
   exists_positiveSurplusPerronWright_radius_relative_bound_of_tendsto)

end Positive

namespace Radius

export PerronWright.CriticalWindowRadiusConversion
  (realScalarRadius criticalQuadraticRate
   realScalarRadius_pos_eventually
   exists_criticalWindowRadius_relative_bound)

end Radius

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The full bounded-surplus radius formula on an arbitrary nonnegative
shrinking window.  The proof performs the finite extraction by induction on
`R`, adding only the new endpoint surplus at each successor step. -/
theorem exists_boundedSurplusPerronWright_radius_relative_bound_uniform_eta
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k r /
            Main.perronWrightRadiusMainTerm M hM k r t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  induction R with
  | zero =>
      obtain ⟨K, hK, hbound⟩ :=
        Main.exists_lowSurplus_unified_radius_relative_bound_uniform_eta M hM
      refine ⟨K, hK, ?_⟩
      intro eta hetaNonneg heta
      have hboundWindow := hbound eta hetaNonneg heta
      filter_upwards [hboundWindow] with k hk
      intro r hr t ht
      exact hk r (by omega) t ht
  | succ R ih =>
      by_cases hRzero : R = 0
      · subst R
        obtain ⟨K, hK, hbound⟩ :=
          Main.exists_lowSurplus_unified_radius_relative_bound_uniform_eta M hM
        refine ⟨K, hK, ?_⟩
        intro eta hetaNonneg heta
        have hboundWindow := hbound eta hetaNonneg heta
        filter_upwards [hboundWindow] with k hk
        intro r hr t ht
        exact hk r (by omega) t ht
      · have hRpos : 0 < R := Nat.pos_of_ne_zero hRzero
        obtain ⟨Kprev, hKprev, hprev⟩ := ih
        obtain ⟨Ktop, hKtop, htop⟩ :=
          Positive.exists_positiveSurplusPerronWright_radius_relative_bound_uniform_eta
            M hM hRpos
        let K : ℝ := Kprev + Ktop
        have hK : 0 < K := add_pos hKprev hKtop
        refine ⟨K, hK, ?_⟩
        intro eta hetaNonneg heta
        have hprevWindow := hprev eta hetaNonneg heta
        have htopWindow := htop eta hetaNonneg heta
        filter_upwards [hprevWindow, htopWindow] with k hkprev hktop
        intro r hr t ht
        let scale : ℝ := eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))
        have hscale : 0 ≤ scale := by
          dsimp only [scale]
          exact add_nonneg (hetaNonneg k)
            (Real.rpow_nonneg (Nat.cast_nonneg k) _)
        by_cases hrtop : r = R + 1
        · subst r
          have h := hktop t ht
          exact h.trans (mul_le_mul_of_nonneg_right
            (by dsimp only [K]; linarith [hKprev]) hscale)
        · have hrprev : r ≤ R := by omega
          have h := hkprev r hrprev t ht
          exact h.trans (mul_le_mul_of_nonneg_right
            (by dsimp only [K]; linarith [hKtop]) hscale)

/-- Compatibility form with a prescribed shrinking window. -/
theorem exists_boundedSurplusPerronWright_radius_relative_bound_of_tendsto
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R : ℕ) (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k r /
            Main.perronWrightRadiusMainTerm M hM k r t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_boundedSurplusPerronWright_radius_relative_bound_uniform_eta
      M hM R
  exact ⟨K, hK, huniform eta hetaNonneg heta⟩

/-- The unified Gaussian main term on the standard critical window. -/
def perronWrightGaussianMainTerm
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (k r : ℕ) (t : ℝ) : ℝ :=
  Main.wrightConstant r *
    (M.beta hM) ^ (((r : ℝ) - 1) / 2) *
    Real.exp (-(k : ℝ)) *
    (k : ℝ) ^ ((k : ℝ) + 3 * (r : ℝ) / 2 - 2) *
    Real.exp (-Radius.criticalQuadraticRate M hM * (k : ℝ) *
      (t - 1) ^ 2)

private theorem rpow_neg_half_eq_inv_sqrt {k : ℕ} (hk : 0 < k) :
    (k : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (k : ℝ))⁻¹ := by
  have hkreal : (0 : ℝ) ≤ k := by exact_mod_cast hk.le
  rw [Real.rpow_neg hkreal, ← Real.sqrt_eq_rpow]

private theorem perronWrightRadiusMainTerm_ne_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k r : ℕ} (hk : 0 < k) {t : ℝ}
    (hrho : 0 < Radius.realScalarRadius M hM t) :
    Main.perronWrightRadiusMainTerm M hM k r t ≠ 0 := by
  have hw : 0 < Main.wrightConstant r := Main.wrightConstant_pos r
  have hbeta : 0 < M.beta hM := M.beta_pos hM
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < Main.perronWrightRadiusMainTerm M hM k r t := by
    unfold Main.perronWrightRadiusMainTerm
      TreePerronWrightFormula.physicalTreeRadius
    positivity
  exact hpos.ne'

private theorem perronWrightGaussianMainTerm_ne_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k r : ℕ} (hk : 0 < k) (t : ℝ) :
    perronWrightGaussianMainTerm M hM k r t ≠ 0 := by
  have hw : 0 < Main.wrightConstant r := Main.wrightConstant_pos r
  have hbeta : 0 < M.beta hM := M.beta_pos hM
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < perronWrightGaussianMainTerm M hM k r t := by
    unfold perronWrightGaussianMainTerm
    positivity
  exact hpos.ne'

private theorem perronWrightRadius_div_gaussian
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k r : ℕ} (hk : 0 < k) (t : ℝ) :
    Main.perronWrightRadiusMainTerm M hM k r t /
        perronWrightGaussianMainTerm M hM k r t =
      (Radius.realScalarRadius M hM t)⁻¹ ^ k /
        Real.exp (-Radius.criticalQuadraticRate M hM * (k : ℝ) *
          (t - 1) ^ 2) := by
  have hw : Main.wrightConstant r ≠ 0 := (Main.wrightConstant_pos r).ne'
  have hbetaPow :
      (M.beta hM) ^ (((r : ℝ) - 1) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (M.beta_pos hM) _).ne'
  have hcommon :
      Main.wrightConstant r *
          (M.beta hM) ^ (((r : ℝ) - 1) / 2) *
          Real.exp (-(k : ℝ)) *
          (k : ℝ) ^ ((k : ℝ) + 3 * (r : ℝ) / 2 - 2) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (Main.wrightConstant_pos r).ne'
          (Real.rpow_pos_of_pos (M.beta_pos hM) _).ne')
        (Real.exp_pos _).ne')
      (Real.rpow_pos_of_pos (by exact_mod_cast hk) _).ne'
  unfold Main.perronWrightRadiusMainTerm
    perronWrightGaussianMainTerm
    TreePerronWrightFormula.physicalTreeRadius
  field_simp [hcommon, hw, hbetaPow]

/-- Uniform bounded-surplus Gaussian formula on the standard critical
window `sqrt k * |t-1| ≤ L`. -/
theorem exists_boundedSurplusPerronWright_gaussian_relative_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
        Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.connectedWeight t k r /
            perronWrightGaussianMainTerm M hM k r t - 1| ≤
          K / Real.sqrt (k : ℝ) := by
  let eta : ℕ → ℝ := fun k ↦
    L * (k : ℝ) ^ (-(1 / 2 : ℝ))
  have hetaNonneg : ∀ k, 0 ≤ eta k := fun k ↦
    mul_nonneg hL (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have heta : Tendsto eta atTop (nhds 0) := by
    have hhalf : Tendsto
        (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
    simpa only [eta, mul_zero] using tendsto_const_nhds.mul hhalf
  obtain ⟨Kradius, hKradius, hradius⟩ :=
    exists_boundedSurplusPerronWright_radius_relative_bound_of_tendsto
      M hM R eta hetaNonneg heta
  obtain ⟨Kconvert, hKconvert, hconvert⟩ :=
    Radius.exists_criticalWindowRadius_relative_bound M hM L hL
  let A : ℝ := Kradius * (L + 1)
  have hA : 0 < A := mul_pos hKradius (by linarith)
  let K : ℝ := A * (1 + Kconvert) + Kconvert
  have hK : 0 < K := by dsimp only [K]; positivity
  have hrhoLocal := Radius.realScalarRadius_pos_eventually M hM
  have hrhoWindow :=
    PerronWright.PositiveSurplusNoncubicPerronWrightBound.shrinkingWindow_eventually_mem_nhds
      eta heta hrhoLocal
  refine ⟨K, hK, ?_⟩
  filter_upwards [hradius, hconvert, hrhoWindow,
    eventually_ge_atTop (1 : ℕ)] with k hkr hkc hkrho hkone
  intro r hr t hwindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  let x : ℝ := (Real.sqrt (k : ℝ))⁻¹
  have hx : 0 ≤ x := inv_nonneg.mpr hsqrt.le
  have hxRpow : (k : ℝ) ^ (-(1 / 2 : ℝ)) = x :=
    rpow_neg_half_eq_inv_sqrt hkpos
  have hxone : x ≤ 1 := by
    rw [← hxRpow]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hkone) (by norm_num)
  have htEta : |t - 1| ≤ eta k := by
    have hdiv := (le_div_iff₀ hsqrt).2 (by
      simpa only [mul_comm] using hwindow)
    rw [div_eq_mul_inv, ← rpow_neg_half_eq_inv_sqrt hkpos] at hdiv
    simpa only [eta] using hdiv
  have hrho : 0 < Radius.realScalarRadius M hM t := hkrho t htEta
  have hRadiusRaw := hkr r hr t htEta
  have hRadius :
      |M.connectedWeight t k r /
          Main.perronWrightRadiusMainTerm M hM k r t - 1| ≤ A * x := by
    calc
      |M.connectedWeight t k r /
          Main.perronWrightRadiusMainTerm M hM k r t - 1| ≤
          Kradius * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
        hRadiusRaw
      _ = A * x := by
        dsimp only [A, eta]
        rw [hxRpow]
        ring
  have hConvert :
      |Main.perronWrightRadiusMainTerm M hM k r t /
          perronWrightGaussianMainTerm M hM k r t - 1| ≤
        Kconvert * x := by
    rw [perronWrightRadius_div_gaussian M hM hkpos t]
    have hc := hkc t hwindow
    simpa only [x, div_eq_mul_inv] using hc
  have hRadiusNe :=
    perronWrightRadiusMainTerm_ne_zero M hM (r := r) hkpos hrho
  have hGaussianNe :=
    perronWrightGaussianMainTerm_ne_zero M hM (r := r) hkpos t
  have hfactor :
      M.connectedWeight t k r /
          perronWrightGaussianMainTerm M hM k r t =
        (M.connectedWeight t k r /
          Main.perronWrightRadiusMainTerm M hM k r t) *
        (Main.perronWrightRadiusMainTerm M hM k r t /
          perronWrightGaussianMainTerm M hM k r t) := by
    field_simp [hRadiusNe, hGaussianNe]
  rw [hfactor]
  have hproduct :=
    PerronWright.RelativeErrorProduct.abs_two_factor_sub_one_le
      hx hxone hA.le hKconvert.le hRadius hConvert
  simpa only [K, x, div_eq_mul_inv] using hproduct

/-- The bounded-surplus Gaussian formula with the window and error written
literally in the `k^(-1/2)` notation of the Perron--Wright theorem. -/
theorem exists_boundedSurplusPerronWright_gaussian_relative_bound_rpow_window
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
        |t - 1| ≤ L * (k : ℝ) ^ (-(1 / 2 : ℝ)) →
        |M.connectedWeight t k r /
            perronWrightGaussianMainTerm M hM k r t - 1| ≤
          K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hmain⟩ :=
    exists_boundedSurplusPerronWright_gaussian_relative_bound
      M hM R L hL
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop (1 : ℕ)] with k hk hkone
  intro r hr t ht
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hx := rpow_neg_half_eq_inv_sqrt (k := k) hkpos
  have hwindow : Real.sqrt (k : ℝ) * |t - 1| ≤ L := by
    calc
      Real.sqrt (k : ℝ) * |t - 1| ≤
          Real.sqrt (k : ℝ) *
            (L * (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left ht hsqrt.le
      _ = L := by
        rw [hx]
        field_simp [hsqrt.ne']
  have hbound := hk r hr t hwindow
  calc
    |M.connectedWeight t k r /
          perronWrightGaussianMainTerm M hM k r t - 1| ≤
        K / Real.sqrt (k : ℝ) := hbound
    _ = K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← hx]

end PerronWright.BoundedSurplusPerronWrightFormula
