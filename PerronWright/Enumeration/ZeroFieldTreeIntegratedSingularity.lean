import PerronWright.Enumeration.ZeroFieldTreeLocalSingularity
import Mathlib.Analysis.Analytic.Order

/-!
# The integrated zero-field tree singularity

This file integrates the differential fold expansion proved in
`ZeroFieldTreeLocalSingularity`.  The normalization is still local: matching
the additive constant to the convergent labelled-tree series is kept as a
separate step.  The point of the result below is that the first omitted term
is genuinely divisible by `X^4`, with an analytic quotient.
-/

open Filter Topology
open scoped Topology ENNReal

noncomputable section

namespace PerronWright.ZeroFieldTreeIntegratedSingularity

open PerronWright.ZeroFieldTreeLocalSingularity

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A normalized local primitive of the zero-field tree differential has the
integrated fold expansion
`-X^2 + (2 gamma / 3) X^3 + X^4 R(X)`.

The proof uses analytic order rather than introducing Taylor coefficients as
new interfaces: after subtracting the displayed polynomial, the derivative
is divisible by `X^3`, so the normalized difference is divisible by `X^4`.
-/
theorem exists_normalized_zeroFieldTree_fold_expansion
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (U R : ℂ → ℂ) (r : ℝ),
      0 < r ∧ U 0 = 0 ∧
      AnalyticOnNhd ℂ U (Metric.ball (0 : ℂ) r) ∧
      AnalyticAt ℂ R 0 ∧
      (∀ X ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt U (treeFoldDerivative M hM X) X) ∧
      ∀ᶠ X : ℂ in 𝓝 0,
        U X = -X ^ 2 +
          (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3 +
          X ^ 4 * R X := by
  obtain ⟨Q, hQa, hQ⟩ :=
    exists_treeFoldDerivative_cubic_remainder M hM
  obtain ⟨U, r, hr, hU0, hUa, hUderiv⟩ :=
    exists_normalized_zeroFieldTree_fold_primitive M hM
  let P : ℂ → ℂ := fun X =>
    -X ^ 2 + (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3
  let W : ℂ → ℂ := fun X => U X - P X
  have hPa : AnalyticAt ℂ P 0 := by
    dsimp only [P]
    fun_prop
  have hWa : AnalyticAt ℂ W 0 := by
    exact (hUa 0 (Metric.mem_ball_self hr)).sub hPa
  have hW0 : W 0 = 0 := by
    simp [W, P, hU0]
  have hUderivNhd : ∀ᶠ X : ℂ in 𝓝 0,
      HasDerivAt U (treeFoldDerivative M hM X) X := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with X hX
    exact hUderiv X hX
  have hWderiv : deriv W =ᶠ[𝓝 0] fun X : ℂ => X ^ 3 * Q X := by
    filter_upwards [hUderivNhd, hQ] with X hUX hQX
    have hPX : HasDerivAt P
        (-2 * X + 2 * (FoldCoefficients.gamma M hM : ℂ) * X ^ 2) X := by
      dsimp only [P]
      have hraw := ((hasDerivAt_id X).pow 2).neg.add
        (((hasDerivAt_id X).pow 3).const_mul
          (2 * (FoldCoefficients.gamma M hM : ℂ) / 3))
      apply hraw.congr_deriv
      norm_num [id]
      ring
    rw [show deriv W X =
        treeFoldDerivative M hM X -
          (-2 * X + 2 * (FoldCoefficients.gamma M hM : ℂ) * X ^ 2) by
      exact (hUX.sub hPX).deriv]
    rw [hQX]
    ring
  have hRHSa : AnalyticAt ℂ (fun X : ℂ => X ^ 3 * Q X) 0 := by
    fun_prop
  have horderDeriv : (3 : ℕ∞) ≤ analyticOrderAt (deriv W) 0 := by
    rw [analyticOrderAt_congr hWderiv]
    exact (natCast_le_analyticOrderAt hRHSa).2
      ⟨Q, hQa, by simp [smul_eq_mul]⟩
  have horderW : (4 : ℕ∞) ≤ analyticOrderAt W 0 := by
    have h := (analyticOrderAt_deriv_ge_iff hWa hW0).mp horderDeriv
    norm_num at h
    exact h
  obtain ⟨R, hRa, hR⟩ :=
    (natCast_le_analyticOrderAt hWa).1 horderW
  refine ⟨U, R, r, hr, hU0, hUa, hRa, hUderiv, ?_⟩
  filter_upwards [hR] with X hRX
  have hWX : W X = X ^ 4 * R X := by
    simpa only [sub_zero, smul_eq_mul] using hRX
  dsimp only [W, P] at hWX
  calc
    U X = X ^ 4 * R X +
        (-X ^ 2 +
          (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3) :=
      sub_eq_iff_eq_add.mp hWX
    _ = -X ^ 2 +
        (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3 +
          X ^ 4 * R X := by ring

end PerronWright.ZeroFieldTreeIntegratedSingularity
