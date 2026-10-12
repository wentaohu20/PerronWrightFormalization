import PerronWright.Enumeration.PositiveSurplusNoncubicPerronWrightBound
import PerronWright.Enumeration.PerronWrightFormulaMainTerm

/-!
# The actual positive-surplus Perron--Wright formula

The exact connected weight is the sum of its cubic and noncubic core
contributions.  The cubic term has the physical Perron--Wright main term;
the noncubic term is one half-step smaller relative to the same denominator.
Combining the two estimates yields the theorem for the actual connected
weight, with the conversion from a complex norm to the real absolute value
made explicit.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology BigOperators ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.PositiveSurplusPerronWrightFormula

open PerronWright.GraphCore

namespace Cubic

export PerronWright.PositiveSurplusCubicPerronWrightFormula
  (scalarCubicPartContribution scalarNoncubicPartContribution
   scalarCubicPartRadiusMainTerm
   scalarCubicPartRadiusMainTerm_eq_exp_rpow
   connectedWeight_eq_scalarCubicPartContribution_add_noncubic
   exists_scalarCubicPart_radius_relative_bound_uniform_eta
   exists_scalarCubicPart_radius_relative_bound_of_tendsto)

end Cubic

namespace Noncubic

export PerronWright.PositiveSurplusNoncubicPerronWrightBound
  (exists_scalarNoncubicPart_cubicRadiusMain_bound_uniform_eta
   exists_scalarNoncubicPart_cubicRadiusMain_bound_of_tendsto)

end Noncubic

namespace Main

export PerronWright.PerronWrightFormulaMainTerm
  (perronWrightRadiusMainTerm perronWrightRadiusMainTerm_positive)

end Main

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- For positive excess, the complex cubic radius main term is exactly the
complexification of the unified real Perron--Wright radius main term. -/
theorem scalarCubicPartRadiusMainTerm_eq_perronWrightRadiusMainTerm
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell k : ℕ} (hell : 0 < ell) (hk : 0 < k) (t : ℝ) :
    Cubic.scalarCubicPartRadiusMainTerm M hM ell k t =
      (Main.perronWrightRadiusMainTerm M hM k (ell + 1) t : ℂ) := by
  have hbeta : 0 ≤ M.beta hM := (M.beta_pos hM).le
  have hsqrtPow :
      Real.sqrt (M.beta hM) ^ ell =
        (M.beta hM) ^ ((ell : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hbeta]
    congr 1
    ring
  have hsqrtCast :
      (Real.sqrt (M.beta hM) : ℂ) ^ ell =
        ((M.beta hM) ^ ((ell : ℝ) / 2) : ℝ) := by
    exact_mod_cast hsqrtPow
  rw [Cubic.scalarCubicPartRadiusMainTerm_eq_exp_rpow
      M hM hell hk t,
    Main.perronWrightRadiusMainTerm_positive M hM hell k t,
    positiveSurplusWrightConstant_eq_ofReal]
  unfold positiveSurplusCubicExponent
    TreePerronWrightFormula.physicalTreeRadius
  rw [hsqrtCast]
  push_cast
  ring

/-- The actual positive-surplus connected weight satisfies the radius form
of the Perron--Wright estimate on every nonnegative shrinking window. -/
theorem exists_positiveSurplusPerronWright_radius_relative_bound_uniform_eta
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, |t - 1| ≤ eta k →
        |M.connectedWeight t k (ell + 1) /
            Main.perronWrightRadiusMainTerm M hM k (ell + 1) t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Kc, hKc, hcubic⟩ :=
    Cubic.exists_scalarCubicPart_radius_relative_bound_uniform_eta
      M hM hell
  obtain ⟨Kn, hKn, hnoncubic⟩ :=
    Noncubic.exists_scalarNoncubicPart_cubicRadiusMain_bound_uniform_eta
      M hM hell
  let K : ℝ := Kc + Kn
  have hK : 0 < K := add_pos hKc hKn
  have htpos : ∀ᶠ t : ℝ in nhds 1, 0 < t :=
    isOpen_Ioi.mem_nhds (by
      simpa only [Set.mem_Ioi] using (show (0 : ℝ) < 1 by norm_num))
  refine ⟨K, hK, ?_⟩
  intro eta hetaNonneg heta
  have hcubicWindow := hcubic eta hetaNonneg heta
  have hnoncubicWindow := hnoncubic eta hetaNonneg heta
  have htposWindow :=
    PerronWright.PositiveSurplusNoncubicPerronWrightBound.shrinkingWindow_eventually_mem_nhds
      eta heta htpos
  filter_upwards [hcubicWindow, hnoncubicWindow, htposWindow,
    eventually_ge_atTop (1 : ℕ)] with k hkc hkn hktpos hkone
  intro t htWindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have ht : 0 < t := hktpos t htWindow
  let main : ℂ :=
    Cubic.scalarCubicPartRadiusMainTerm M hM ell k t
  let scale : ℝ := eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))
  have hsplit :=
    Cubic.connectedWeight_eq_scalarCubicPartContribution_add_noncubic
      M t ht ell k
  have hc := hkc t htWindow
  have hn := hkn t htWindow
  have hcomplex :
      ‖(M.connectedWeight t k (ell + 1) : ℂ) / main - 1‖ ≤
        K * scale := by
    calc
      ‖(M.connectedWeight t k (ell + 1) : ℂ) / main - 1‖ =
          ‖(Cubic.scalarCubicPartContribution M t ell k / main - 1) +
            Cubic.scalarNoncubicPartContribution M t ell k / main‖ := by
        rw [hsplit]
        congr 1
        ring
      _ ≤ ‖Cubic.scalarCubicPartContribution M t ell k / main - 1‖ +
          ‖Cubic.scalarNoncubicPartContribution M t ell k / main‖ :=
        norm_add_le _ _
      _ ≤ Kc * scale + Kn * scale := by
        exact add_le_add (by simpa only [main, scale] using hc)
          (by simpa only [main, scale] using hn)
      _ = K * scale := by dsimp only [K]; ring
  have hmain :=
    scalarCubicPartRadiusMainTerm_eq_perronWrightRadiusMainTerm
      M hM hell hkpos t
  dsimp only [main] at hcomplex
  rw [hmain] at hcomplex
  have hcast :
      ((M.connectedWeight t k (ell + 1) /
          Main.perronWrightRadiusMainTerm M hM k (ell + 1) t - 1 : ℝ) : ℂ) =
        (M.connectedWeight t k (ell + 1) : ℂ) /
          (Main.perronWrightRadiusMainTerm M hM k (ell + 1) t : ℂ) - 1 := by
    push_cast
    rfl
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs] at hcomplex
  simpa only [K, scale] using hcomplex

/-- Compatibility form with a prescribed shrinking window. -/
theorem exists_positiveSurplusPerronWright_radius_relative_bound_of_tendsto
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell)
    (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ, |t - 1| ≤ eta k →
        |M.connectedWeight t k (ell + 1) /
            Main.perronWrightRadiusMainTerm M hM k (ell + 1) t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_positiveSurplusPerronWright_radius_relative_bound_uniform_eta
      M hM hell
  exact ⟨K, hK, huniform eta hetaNonneg heta⟩

end PerronWright.PositiveSurplusPerronWrightFormula
