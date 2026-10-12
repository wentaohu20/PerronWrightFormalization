import PerronWright.Analysis.TreeFoldCurvature
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

open MeasureTheory PerronWright
open scoped Topology ContDiff

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.TreeFoldSquareRoot

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The local scalar radius deficit has an analytic nonvanishing quadratic factor.
This is obtained from the actual fold curve and its proved curvature. -/
theorem radius_deficit_factorization (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ H : ℂ → ℂ,
      AnalyticAt ℂ H 0 ∧ H 0 = (M.beta hM : ℂ) / 2 ∧
      ∀ s : ℂ, 1 - TreeFoldCurvature.radiusSlice M hM s = s ^ 2 * H s := by
  let z := TreeFoldCurvature.radiusSlice M hM
  let f : ℂ → ℂ := fun s ↦ 1 - z s
  have hf : AnalyticAt ℂ f 0 :=
    analyticAt_const.sub (TreeFoldCurvature.radiusSlice_analytic M hM)
  have hf0 : f 0 = 0 := by
    change 1 - TreeFoldCurvature.radiusSlice M hM 0 = 0
    rw [TreeFoldCurvature.radiusSlice_base]
    ring
  have hf1 : deriv f 0 = 0 := by
    rw [show f = (fun s : ℂ ↦ 1 - z s) from rfl, deriv_const_sub,
      TreeFoldCurvature.radiusSlice_deriv]
    simp
  have hf2 : deriv (deriv f) 0 = (M.beta hM : ℂ) := by
    change deriv (deriv (fun s : ℂ ↦ 1 - z s)) 0 = _
    rw [deriv_const_sub' (1 : ℂ)]
    change deriv (-(deriv z)) 0 = _
    rw [deriv.neg]
    rw [TreeFoldCurvature.radiusSlice_second_deriv]
    ring
  obtain ⟨R, hRa, hR⟩ := hf.exists_eq_sum_add_pow_mul 3
  let H : ℂ → ℂ := fun s ↦ (M.beta hM : ℂ) / 2 + s * R s
  have hHa : AnalyticAt ℂ H 0 := by
    unfold H
    exact analyticAt_const.add (analyticAt_id.mul hRa)
  have hH0 : H 0 = (M.beta hM : ℂ) / 2 := by
    simp only [H, zero_mul, add_zero]
  refine ⟨H, hHa, hH0, ?_⟩
  intro s
  have hpoly :
      (∑ i ∈ Finset.range 3, (s ^ i / i.factorial) • iteratedDeriv i f 0) =
        (M.beta hM : ℂ) / 2 * s ^ 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      iteratedDeriv_succ, iteratedDeriv_zero]
    simp only [hf0, hf1, hf2]
    norm_num
    ring
  have hs := hR s
  rw [hpoly] at hs
  change f s = _ at hs
  change f s = s ^ 2 * H s
  rw [hs]
  simp only [H, smul_eq_mul]
  ring

/-- The quadratic factor has a canonical analytic square root, normalized by the
positive Perron--Wright fold coefficient. -/
theorem analytic_square_root_of_quadratic_factor (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (H : ℂ → ℂ) (hHa : AnalyticAt ℂ H 0)
    (hH0 : H 0 = (M.beta hM : ℂ) / 2) :
    ∃ B : ℂ → ℂ,
      AnalyticAt ℂ B 0 ∧
      B 0 = (FoldCoefficients.gamma M hM : ℂ)⁻¹ ∧
      ∀ᶠ s in nhds (0 : ℂ), B s ^ 2 = H s := by
  let β : ℂ := M.beta hM
  let γ : ℂ := FoldCoefficients.gamma M hM
  have hβ : β ≠ 0 := Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne'
  have hγ : γ ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FoldCoefficients.gamma_pos M hM).ne'
  have hγβ : γ ^ 2 * β = 2 := by
    change (FoldCoefficients.gamma M hM : ℂ) ^ 2 * (M.beta hM : ℂ) = 2
    exact_mod_cast FoldCoefficients.gamma_sq_mul_beta M hM
  have hscale : γ⁻¹ ^ 2 * (2 / β) = 1 := by
    field_simp [hγ, hβ]
    exact hγβ.symm
  let Q : ℂ → ℂ := fun s ↦ H s * (2 / β)
  have hQa : AnalyticAt ℂ Q 0 := hHa.mul analyticAt_const
  have hQ0 : Q 0 = 1 := by
    change H 0 * (2 / β) = 1
    rw [hH0]
    change (β / 2) * (2 / β) = 1
    field_simp [hβ]
  have hQslit : Q 0 ∈ Complex.slitPlane := by
    rw [hQ0]
    exact Complex.one_mem_slitPlane
  let B : ℂ → ℂ := fun s ↦ γ⁻¹ * Complex.exp (Complex.log (Q s) / 2)
  have hBa : AnalyticAt ℂ B 0 := by
    apply analyticAt_const.mul
    exact ((hQa.clog hQslit).div_const).cexp'
  have hB0 : B 0 = γ⁻¹ := by
    simp [B, hQ0]
  refine ⟨B, hBa, hB0, ?_⟩
  have hQnz : ∀ᶠ s in nhds (0 : ℂ), Q s ≠ 0 := by
    have := hQa.continuousAt.eventually_ne (by rw [hQ0]; exact one_ne_zero)
    simpa using this
  filter_upwards [hQnz] with s hs
  have hsqexp : (Complex.exp (Complex.log (Q s) / 2)) ^ 2 =
      Complex.exp (Complex.log (Q s)) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  calc
    B s ^ 2 = γ⁻¹ ^ 2 * (Complex.exp (Complex.log (Q s) / 2)) ^ 2 := by
      simp only [B, mul_pow]
    _ = γ⁻¹ ^ 2 * Q s := by rw [hsqexp, Complex.exp_log hs]
    _ = H s := by
      change γ⁻¹ ^ 2 * (H s * (2 / β)) = H s
      calc
        _ = (γ⁻¹ ^ 2 * (2 / β)) * H s := by ring
        _ = H s := by rw [hscale, one_mul]

/-- Inverting the genuine fold coordinate `s ↦ s B(s)` gives the local
square-root parameter, with derivative equal to the exact constant `γ`. -/
theorem analytic_fold_coordinate_inverse (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (B : ℂ → ℂ) (hBa : AnalyticAt ℂ B 0)
    (hB0 : B 0 = (FoldCoefficients.gamma M hM : ℂ)⁻¹) :
    ∃ s : ℂ → ℂ,
      AnalyticAt ℂ s 0 ∧ s 0 = 0 ∧
      deriv s 0 = (FoldCoefficients.gamma M hM : ℂ) ∧
      ∀ᶠ X in nhds (0 : ℂ), s X * B (s X) = X := by
  let γ : ℂ := FoldCoefficients.gamma M hM
  have hγ : γ ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FoldCoefficients.gamma_pos M hM).ne'
  have hγinv : γ⁻¹ ≠ 0 := inv_ne_zero hγ
  let Q : ℂ → ℂ := id * B
  have hQa : AnalyticAt ℂ Q 0 := analyticAt_id.mul hBa
  have hQ0 : Q 0 = 0 := by simp [Q]
  have hQderiv : HasStrictDerivAt Q γ⁻¹ 0 := by
    simpa only [Q, hB0, id_eq, one_mul, zero_mul, add_zero] using
      (hasStrictDerivAt_id (0 : ℂ)).mul hBa.hasStrictDerivAt
  have hQd : deriv Q 0 = γ⁻¹ := hQderiv.hasDerivAt.deriv
  have hQdne : deriv Q 0 ≠ 0 := by rw [hQd]; exact hγinv
  let s : ℂ → ℂ := hQa.hasStrictDerivAt.localInverse Q (deriv Q 0) 0 hQdne
  have hsa : AnalyticAt ℂ s 0 := by
    have hsa' : AnalyticAt ℂ s (Q 0) :=
      hQa.analyticAt_localInverse hQdne
    simpa only [hQ0] using hsa'
  have hs0 : s 0 = 0 := by
    have hs0' : s (Q 0) = 0 :=
      (hQa.hasStrictDerivAt.eventually_left_inverse hQdne).self_of_nhds
    simpa only [hQ0] using hs0'
  have hsd : deriv s 0 = γ := by
    have h := (hQa.hasStrictDerivAt.to_localInverse hQdne).hasDerivAt.deriv
    simpa only [hQ0, hQd, inv_inv] using h
  refine ⟨s, hsa, hs0, hsd, ?_⟩
  have hinv := hQa.hasStrictDerivAt.eventually_right_inverse hQdne
  rw [hQ0] at hinv
  filter_upwards [hinv] with X hX
  exact hX

/-- The actual zero-field tree equation has an analytic branch in
`X = √(1-z)` with its exact Perron leading derivative. -/
theorem actual_zero_field_fold_chart (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ T : ℂ → C(S, ℂ),
      AnalyticAt ℂ T 0 ∧ T 0 = 1 ∧
      deriv T 0 = (-(FoldCoefficients.gamma M hM : ℂ)) •
        M.complexPerronFunction hM ∧
      ∀ᶠ X in nhds (0 : ℂ),
        T X = (1 - X ^ 2) • NormedSpace.exp
          (-TreeCritical.degree M + M.kernel.complexActionCLM M.mu (T X)) := by
  obtain ⟨H, hHa, hH0, hFactor⟩ := radius_deficit_factorization M hM
  obtain ⟨B, hBa, hB0, hBsq⟩ :=
    analytic_square_root_of_quadratic_factor M hM H hHa hH0
  obtain ⟨s, hsa, hs0, hsd, hInv⟩ :=
    analytic_fold_coordinate_inverse M hM B hBa hB0
  let γ : ℂ := FoldCoefficients.gamma M hM
  have hnega : AnalyticAt ℂ (fun X : ℂ ↦ -X) 0 :=
    analyticAt_id.neg
  have hnegd : HasDerivAt (fun X : ℂ ↦ -X) (-1) 0 :=
    (hasDerivAt_id (0 : ℂ)).neg
  have hnegt : Filter.Tendsto (fun X : ℂ ↦ -X) (nhds 0) (nhds 0) :=
    by simpa only [neg_zero] using hnega.continuousAt.tendsto
  have hSnegt : Filter.Tendsto (fun X : ℂ ↦ s (-X)) (nhds 0) (nhds 0) := by
    have ht := hsa.continuousAt.tendsto.comp hnegt
    simpa only [hs0, Function.comp_def] using ht
  have hSnega : AnalyticAt ℂ (fun X : ℂ ↦ s (-X)) 0 := by
    have hsa' : AnalyticAt ℂ s (-(0 : ℂ)) := by simpa using hsa
    simpa only [Function.comp_def] using hsa'.comp hnega
  have hSnegd : HasDerivAt (fun X : ℂ ↦ s (-X)) (-γ) 0 := by
    have hs' := hsa.hasStrictDerivAt.hasDerivAt
    rw [hsd] at hs'
    have hs'' : HasDerivAt s γ (-(0 : ℂ)) := by simpa using hs'
    have hc := hs''.comp 0 hnegd
    simpa only [Function.comp_def, mul_neg, mul_one] using hc
  let T : ℂ → C(S, ℂ) := fun X ↦ TreeFoldCurvature.profileSlice M hM (s (-X))
  have hTa : AnalyticAt ℂ T 0 := by
    have hc := (TreeFoldCurvature.profileSlice_analytic M hM).comp_of_eq
      hSnega (by simp only [neg_zero, hs0])
    simpa only [T, Function.comp_def] using hc
  have hT0 : T 0 = 1 := by
    simp only [T, neg_zero, hs0, TreeFoldCurvature.profileSlice_base]
  have hTd : deriv T 0 = (-γ) • M.complexPerronFunction hM := by
    have hp : HasDerivAt (TreeFoldCurvature.profileSlice M hM)
        (M.complexPerronFunction hM) 0 := by
      have h := (TreeFoldCurvature.profileSlice_analytic M hM).hasStrictDerivAt.hasDerivAt
      rw [TreeFoldCurvature.profileSlice_deriv M hM] at h
      exact h
    have hp' : HasDerivAt (TreeFoldCurvature.profileSlice M hM)
        (M.complexPerronFunction hM) (s (-(0 : ℂ))) := by
      simpa only [neg_zero, hs0] using hp
    have hc := hp'.scomp 0 hSnegd
    simpa only [T, hs0, neg_zero, Function.comp_def] using hc.deriv
  refine ⟨T, hTa, hT0, hTd, ?_⟩
  have hBsq' := hSnegt.eventually hBsq
  have hInv' := hnegt.eventually hInv
  have hFold' := hSnegt.eventually (TreeFoldCurvature.foldSlice_equation M hM)
  filter_upwards [hBsq', hInv', hFold'] with X hBs hIs hFs
  have hz : TreeFoldCurvature.radiusSlice M hM (s (-X)) = 1 - X ^ 2 := by
    have hh : 1 - TreeFoldCurvature.radiusSlice M hM (s (-X)) = X ^ 2 := calc
      _ = (s (-X)) ^ 2 * H (s (-X)) := hFactor (s (-X))
      _ = (s (-X)) ^ 2 * B (s (-X)) ^ 2 := by rw [hBs]
      _ = (s (-X) * B (s (-X))) ^ 2 := by ring
      _ = X ^ 2 := by rw [hIs]; ring
    linear_combination -hh
  change TreeFoldCurvature.profileSlice M hM (s (-X)) = _ at hFs
  rw [hz] at hFs
  exact hFs

end PerronWright.TreeFoldSquareRoot
