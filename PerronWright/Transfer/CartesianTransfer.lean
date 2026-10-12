import PerronWright.Transfer.CartesianGlobalContour

/-!
Final Banach-valued Cartesian transfer step.

The only contour identity used below is
`banachCartesianGlobalContourIdentity`, which has already been proved from
the six explicit radial strips.  The fixed outer-arc bound is discharged
internally from the same power bound used on the local keyhole.
-/

open Complex MeasureTheory Set Metric Filter Asymptotics
open scoped Interval Topology
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- Cauchy's formula converts the exact three-piece Cartesian contour
identity into the corresponding exact Taylor-coefficient identity. -/
theorem banachCartesianTaylorCoefficient_identity
    {F : ℂ → E} {M eta m : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hrhoM : cartesianDetourRadius n ≤ M)
    (hMeta : M < eta) (heta : 1 / (n : ℝ) < eta)
    (hm0 : 0 ≤ m) (hm43 : m < 4 / 3)
    (hF : DifferentiableOn ℂ F (cartesianDelta eta m)) :
    (2 * Real.pi * I) • banachTaylorCoefficient F n +
        banachCartesianLocalKeyhole F M n +
        banachCartesianFixedOuterArcIntegral F M n = 0 := by
  have hrho : 0 < cartesianDetourRadius n := by
    dsimp [cartesianDetourRadius]
    positivity
  have hM : 0 < M := hrho.trans_le hrhoM
  have heta0 : 0 < eta := hM.trans hMeta
  have hdisc : Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆
      cartesianDelta eta m := by
    apply Set.Subset.trans _ (unit_ball_subset_cartesianDelta heta0)
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have hz' : ‖z‖ ≤ (1 / 2 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  have hcauchy :
      (∮ z in C((0 : ℂ), (1 / 2 : ℝ)),
          banachCoefficientIntegrand F n z) =
        (2 * Real.pi * I) • banachTaylorCoefficient F n := by
    simpa only [banachCoefficientIntegrand] using
      (circleIntegral_eq_banachTaylorCoefficient
        (F := F) (R := (1 / 2 : ℝ)) (by norm_num)
        (hF.mono hdisc) n)
  have hglobal := banachCartesianGlobalContourIdentity
    (F := F) (M := M) (eta := eta) (m := m) (n := n)
    hn hrhoM hMeta heta hm0 hm43 hF
  rw [hcauchy] at hglobal
  exact hglobal

omit [NormedSpace ℂ E] [CompleteSpace E] in
/-- The power bound on the Cartesian Delta-domain automatically gives a
fixed bound on the major outer arc.  Thus no separate outer-bound interface
is needed by the final transfer theorem. -/
theorem banachCartesianOuterArc_power_bound
    {F : ℂ → E} {M eta m a : ℝ}
    (hM : 0 < M) (hMeta : M < eta)
    (hm43 : m < 4 / 3) (ha : 0 ≤ a)
    (hF : ∀ z ∈ cartesianDelta eta m,
      ‖F z‖ ≤ ‖z - 1‖ ^ a) :
    ∀ z ∈ cartesianOuterMajorArc M,
      ‖F z‖ ≤ (cartesianOuterRadius M + 1) ^ a := by
  intro z hz
  have hzDelta : z ∈ cartesianDelta eta m :=
    cartesianOuterMajorArc_subset_cartesianDelta hM hMeta hm43 hz
  calc
    ‖F z‖ ≤ ‖z - 1‖ ^ a := hF z hzDelta
    _ ≤ (cartesianOuterRadius M + 1) ^ a := by
      apply Real.rpow_le_rpow (norm_nonneg _) _ ha
      calc
        ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = cartesianOuterRadius M + 1 := by
          rw [hz.1, norm_one]

/-- For all sufficiently large indices, the scaled Taylor coefficient plus
the local keyhole is exactly the negative fixed outer arc. -/
theorem banachCartesianTaylorRemainder_eventuallyEq
    {F : ℂ → E} {M eta m : ℝ}
    (hM : 0 < M) (hMeta : M < eta)
    (hm0 : 0 ≤ m) (hm43 : m < 4 / 3)
    (hF : DifferentiableOn ℂ F (cartesianDelta eta m)) :
    (fun n : ℕ ↦
      (2 * Real.pi * I) • banachTaylorCoefficient F n +
        banachCartesianLocalKeyhole F M n) =ᶠ[Filter.atTop]
      (fun n : ℕ ↦ -banachCartesianFixedOuterArcIntegral F M n) := by
  have heta0 : 0 < eta := hM.trans hMeta
  have hsmallM : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n : ℝ) < M := by
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds hM)
    simpa only [one_div] using ht
  have hsmallEta : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n : ℝ) < eta := by
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds heta0)
    simpa only [one_div] using ht
  filter_upwards [hsmallM, hsmallEta,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hnM hnEta hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hrhoM : cartesianDetourRadius n ≤ M := by
    calc
      cartesianDetourRadius n =
          (1 / 4 : ℝ) * (1 / (n : ℝ)) := by
            dsimp [cartesianDetourRadius]
            ring
      _ ≤ 1 / (n : ℝ) := by
        nlinarith [one_div_pos.mpr hnreal]
      _ ≤ M := hnM.le
  exact eq_neg_of_add_eq_zero_left
    (banachCartesianTaylorCoefficient_identity
      (F := F) (M := M) (eta := eta) (m := m) (n := n)
      hnpos hrhoM hMeta hnEta hm0 hm43 hF)

/-- The outer arc is negligible at the natural local-keyhole scale.  This
is the Banach-valued Taylor-coefficient remainder estimate. -/
theorem banachCartesianTaylorRemainder_isLittleO
    {F : ℂ → E} {M eta m a : ℝ}
    (hM : 0 < M) (hMeta : M < eta)
    (hm0 : 0 ≤ m) (hm43 : m < 4 / 3) (ha : 0 ≤ a)
    (hFdiff : DifferentiableOn ℂ F (cartesianDelta eta m))
    (hFpower : ∀ z ∈ cartesianDelta eta m,
      ‖F z‖ ≤ ‖z - 1‖ ^ a) :
    (fun n : ℕ ↦
      (2 * Real.pi * I) • banachTaylorCoefficient F n +
        banachCartesianLocalKeyhole F M n) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(a + 1))) := by
  let B : ℝ := (cartesianOuterRadius M + 1) ^ a
  have hB : 0 ≤ B := by
    dsimp [B]
    apply Real.rpow_nonneg
    linarith [cartesianOuterRadius_gt_one hM]
  have hFouter : ∀ z ∈ cartesianOuterMajorArc M, ‖F z‖ ≤ B := by
    simpa only [B] using
      (banachCartesianOuterArc_power_bound
        (F := F) hM hMeta hm43 ha hFpower)
  have houter := banachCartesianFixedOuterArcIntegral_isLittleO
    (F := F) hM hB hFouter (-(a + 1))
  have heq := banachCartesianTaylorRemainder_eventuallyEq
    (F := F) hM hMeta hm0 hm43 hFdiff
  apply houter.neg_left.congr'
  · exact heq.symm
  · exact Filter.EventuallyEq.refl _ _

/-- Full minimal Banach-valued Cartesian transfer: the local keyhole gives
the natural polynomial scale, while the fixed outer arc is a little-oh
remainder at that scale. -/
theorem banachCartesianTaylorCoefficient_transfer
    {F : ℂ → E} {M eta m a : ℝ}
    (hM : 0 < M) (hM1 : M ≤ 1) (hMeta : M < eta)
    (hm0 : 0 ≤ m) (hm43 : m < 4 / 3) (ha : 0 ≤ a)
    (hFdiff : DifferentiableOn ℂ F (cartesianDelta eta m))
    (hFpower : ∀ z ∈ cartesianDelta eta m,
      ‖F z‖ ≤ ‖z - 1‖ ^ a) :
    ((fun n : ℕ ↦
        (2 * Real.pi * I) • banachTaylorCoefficient F n +
          banachCartesianLocalKeyhole F M n) =o[Filter.atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(a + 1)))) ∧
      ((fun n : ℕ ↦ banachTaylorCoefficient F n) =O[Filter.atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(a + 1)))) := by
  have hrem := banachCartesianTaylorRemainder_isLittleO
    (F := F) hM hMeta hm0 hm43 ha hFdiff hFpower
  refine ⟨hrem, ?_⟩
  have hlocal := banachCartesianLocalKeyhole_isBigO
    (F := F) hM hM1 hMeta hm43 ha hFpower
  have hscaledSum := hrem.isBigO
  have hscaled :
      (fun n : ℕ ↦
        (2 * Real.pi * I) • banachTaylorCoefficient F n) =O[Filter.atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(a + 1))) := by
    have hdiff := hscaledSum.sub hlocal
    apply hdiff.congr' _ (Filter.EventuallyEq.refl _ _)
    filter_upwards with n
    simp
  have hscalar : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    have hpi : (Real.pi : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero htwo hpi) I_ne_zero
  exact (isBigO_const_smul_left hscalar).mp hscaled

end PerronWright.Transfer
