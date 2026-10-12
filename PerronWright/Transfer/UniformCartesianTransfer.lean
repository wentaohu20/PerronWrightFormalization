import PerronWright.Transfer.CartesianTransfer

/-!
# A family-uniform Cartesian transfer bound

`banachCartesianTaylorCoefficient_transfer` gives a Big-O estimate for one
Banach-valued function.  Applying it separately to a family does not by
itself produce one common Big-O witness.  This file proves the genuinely
uniform quantifier order directly from the exact Cartesian contour identity
and the explicit local-keyhole and outer-arc estimates.

No compactness assumption is made on the index type.  In particular, the
theorem applies to a family indexed by an infinite-dimensional field ball.
-/

open Complex MeasureTheory Set Metric Filter Asymptotics
open scoped Interval Topology

noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The explicit local-keyhole estimate has one Big-O witness for every
member of a family satisfying the same power bound. -/
private theorem exists_uniform_banachCartesianLocalKeyhole_bound
    {ι : Type*} {F : ι → ℂ → E} {M eta m a : ℝ}
    (hM : 0 < M) (hM1 : M ≤ 1) (hMeta : M < eta)
    (hm43 : m < 4 / 3) (ha : 0 ≤ a)
    (hFpower : ∀ i, ∀ z ∈ cartesianDelta eta m,
      ‖F i z‖ ≤ ‖z - 1‖ ^ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ i : ι,
        ‖banachCartesianLocalKeyhole (F i) M n‖ ≤
          K * (n : ℝ) ^ (-(a + 1)) := by
  let K : ℝ :=
    2 * ((4 : ℝ) ^ (a + 1) * Real.Gamma (a + 1)) +
      6 * Real.exp 2 * ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a)
  have hK : 0 ≤ K := by
    have hapos : 0 < a + 1 := by linarith
    have hfour : 0 ≤ (4 : ℝ) ^ (a + 1) :=
      Real.rpow_nonneg (by norm_num) _
    have hGamma : 0 ≤ Real.Gamma (a + 1) :=
      (Real.Gamma_pos_of_pos hapos).le
    have hhalf : 0 ≤ (1 / 2 : ℝ) ^ a :=
      Real.rpow_nonneg (by norm_num) _
    dsimp only [K]
    exact add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg hfour hGamma))
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.exp_pos 2).le)
        (mul_nonneg (by norm_num) hhalf))
  have hsmallM : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < M := by
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds hM)
    simpa only [one_div] using ht
  have heta : 0 < eta := hM.trans hMeta
  have hsmallEta : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < eta := by
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds heta)
    simpa only [one_div] using ht
  refine ⟨K, hK, ?_⟩
  filter_upwards [hsmallM, hsmallEta,
    eventually_ge_atTop (1 : ℕ)] with n hnM hnEta hn
  intro i
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hrhoInv : cartesianDetourRadius n ≤ 1 / (n : ℝ) := by
    calc
      cartesianDetourRadius n =
          (1 / 4 : ℝ) * (1 / (n : ℝ)) := by
            dsimp only [cartesianDetourRadius]
            field_simp
      _ ≤ 1 / (n : ℝ) := by
        nlinarith [one_div_pos.mpr hnreal]
  have hrhoM : cartesianDetourRadius n ≤ M := hrhoInv.trans hnM.le
  have hb := banachCartesianLocalKeyhole_bound
    hM1 hMeta hm43 ha hnpos hrhoM hnEta (hFpower i)
  calc
    ‖banachCartesianLocalKeyhole (F i) M n‖ ≤
        2 * ((1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) *
          Real.Gamma (a + 1)) +
          6 * cartesianDetourRadius n *
            (Real.exp 2 * (2 * cartesianDetourRadius n) ^ a) := hb
    _ = 2 * (((4 : ℝ) ^ (a + 1) *
          (n : ℝ) ^ (-(a + 1))) * Real.Gamma (a + 1)) +
        6 * Real.exp 2 *
          ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ a *
            (n : ℝ) ^ (-(a + 1))) := by
      rw [cartesianRay_scale_eq a hnpos]
      calc
        2 * (4 ^ (a + 1) * (n : ℝ) ^ (-(a + 1)) *
              Real.Gamma (a + 1)) +
            6 * cartesianDetourRadius n *
              (Real.exp 2 * (2 * cartesianDetourRadius n) ^ a) =
            2 * (4 ^ (a + 1) * (n : ℝ) ^ (-(a + 1)) *
              Real.Gamma (a + 1)) +
            6 * Real.exp 2 *
              (cartesianDetourRadius n *
                (2 * cartesianDetourRadius n) ^ a) := by ring_nf
        _ = _ := by rw [cartesianDetour_scale_eq a hnpos]
    _ = K * (n : ℝ) ^ (-(a + 1)) := by
      dsimp only [K]
      ring_nf

omit [CompleteSpace E] in
/-- The fixed outer arc also has one algebraic bound for an arbitrary
family under the same normalized power estimate. -/
private theorem exists_uniform_banachCartesianOuterArc_bound
    {ι : Type*} {F : ι → ℂ → E} {M eta m a : ℝ}
    (hM : 0 < M) (hMeta : M < eta)
    (hm43 : m < 4 / 3) (ha : 0 ≤ a)
    (hFpower : ∀ i, ∀ z ∈ cartesianDelta eta m,
      ‖F i z‖ ≤ ‖z - 1‖ ^ a) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ i : ι,
        ‖banachCartesianFixedOuterArcIntegral (F i) M n‖ ≤
          K * (n : ℝ) ^ (-(a + 1)) := by
  let R : ℝ := cartesianOuterRadius M
  let Bouter : ℝ := (R + 1) ^ a
  have hR : 1 < R := by
    simpa only [R] using cartesianOuterRadius_gt_one hM
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hBouter : 0 ≤ Bouter := by
    dsimp only [Bouter]
    exact Real.rpow_nonneg (by linarith) _
  have htheta : cartesianOuterAngle M ≤
      2 * Real.pi - cartesianOuterAngle M :=
    cartesianOuterAngle_interval_nonempty M
  let A : ℝ :=
    ((2 * Real.pi - cartesianOuterAngle M) -
        cartesianOuterAngle M) * (R * Bouter)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (sub_nonneg.mpr htheta)
      (mul_nonneg hR0.le hBouter)
  let c : ℝ := Real.log R / 2
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (Real.log_pos hR) (by norm_num)
  let outerMajor : ℕ → ℝ := fun n ↦
    A * Real.exp (-(c * (n : ℝ)))
  have hmajorRate : outerMajor =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(a + 1))) := by
    have h := (exp_neg_nat_isLittleO_rpow hc (-(a + 1))).isBigO
      |>.const_mul_left A
    simpa only [outerMajor] using h
  rw [isBigO_iff'] at hmajorRate
  obtain ⟨K, hK, hmajorBound⟩ := hmajorRate
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmajorBound] with n hn
  intro i
  have hFouter : ∀ z ∈ cartesianOuterMajorArc M,
      ‖F i z‖ ≤ Bouter := by
    simpa only [Bouter, R] using
      (banachCartesianOuterArc_power_bound
        (F := F i) hM hMeta hm43 ha (hFpower i))
  have houter := banachCartesianFixedOuterArcIntegral_bound
    (F := F i) hM hBouter hFouter (n := n)
  have houterMajor :
      ‖banachCartesianFixedOuterArcIntegral (F i) M n‖ ≤
        outerMajor n := by
    calc
      ‖banachCartesianFixedOuterArcIntegral (F i) M n‖ ≤
          ((2 * Real.pi - cartesianOuterAngle M) -
              cartesianOuterAngle M) *
            (cartesianOuterRadius M * Bouter *
              Real.exp (-((n : ℝ) *
                (Real.log (cartesianOuterRadius M) / 2)))) := houter
      _ = outerMajor n := by
        dsimp only [outerMajor, A, c, R]
        ring_nf
  have hmajorNonneg : 0 ≤ outerMajor n := by
    dsimp only [outerMajor]
    exact mul_nonneg hA (Real.exp_pos _).le
  have hscaleNonneg :
      0 ≤ (n : ℝ) ^ (-(a + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc
    ‖banachCartesianFixedOuterArcIntegral (F i) M n‖ ≤
        outerMajor n := houterMajor
    _ = ‖outerMajor n‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hmajorNonneg]
    _ ≤ K * ‖(n : ℝ) ^ (-(a + 1))‖ := hn
    _ = K * (n : ℝ) ^ (-(a + 1)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hscaleNonneg]

/-- Family-uniform Banach-valued Cartesian transfer.  The constants and
the eventual threshold are chosen before the family index. -/
theorem exists_uniform_banachCartesianTaylorCoefficient_bound
    {ι : Type*} {F : ι → ℂ → E} {M eta m a : ℝ}
    (hM : 0 < M) (hM1 : M ≤ 1) (hMeta : M < eta)
    (hm0 : 0 ≤ m) (hm43 : m < 4 / 3) (ha : 0 ≤ a)
    (hFdiff : ∀ i, DifferentiableOn ℂ (F i) (cartesianDelta eta m))
    (hFpower : ∀ i, ∀ z ∈ cartesianDelta eta m,
      ‖F i z‖ ≤ ‖z - 1‖ ^ a) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ i : ι,
        ‖banachTaylorCoefficient (F i) n‖ ≤
          K * (n : ℝ) ^ (-(a + 1)) := by
  obtain ⟨Klocal, hKlocal, hlocal⟩ :=
    exists_uniform_banachCartesianLocalKeyhole_bound
      hM hM1 hMeta hm43 ha hFpower
  obtain ⟨Kouter, hKouter, houter⟩ :=
    exists_uniform_banachCartesianOuterArc_bound
      hM hMeta hm43 ha hFpower
  have heta : 0 < eta := hM.trans hMeta
  have hsmallM : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < M := by
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds hM)
    simpa only [one_div] using ht
  have hsmallEta : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < eta := by
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds heta)
    simpa only [one_div] using ht
  let cNorm : ℝ := ‖(2 * Real.pi * I : ℂ)‖
  have hcNorm : 0 < cNorm := by
    dsimp only [cNorm]
    exact norm_pos_iff.mpr (by simp [Real.pi_ne_zero])
  let K : ℝ := (Klocal + Kouter) / cNorm
  have hK : 0 < K := by
    dsimp only [K]
    exact div_pos (add_pos_of_nonneg_of_pos hKlocal hKouter) hcNorm
  refine ⟨K, hK, ?_⟩
  filter_upwards [hlocal, houter, hsmallM, hsmallEta,
    eventually_ge_atTop (1 : ℕ)] with n hnLocal hnOuter hnM hnEta hn
  intro i
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hrhoM : cartesianDetourRadius n ≤ M := by
    calc
      cartesianDetourRadius n =
          (1 / 4 : ℝ) * (1 / (n : ℝ)) := by
            dsimp only [cartesianDetourRadius]
            field_simp
      _ ≤ 1 / (n : ℝ) := by
        nlinarith [one_div_pos.mpr hnreal]
      _ ≤ M := hnM.le
  have hid := banachCartesianTaylorCoefficient_identity
    (F := F i) (M := M) (eta := eta) (m := m) (n := n)
    hnpos hrhoM hMeta hnEta hm0 hm43 (hFdiff i)
  have heq :
      (2 * Real.pi * I) • banachTaylorCoefficient (F i) n =
        -(banachCartesianLocalKeyhole (F i) M n +
          banachCartesianFixedOuterArcIntegral (F i) M n) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc] using hid
  have hscaleNonneg :
      0 ≤ (n : ℝ) ^ (-(a + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hscaled :
      cNorm * ‖banachTaylorCoefficient (F i) n‖ ≤
        (Klocal + Kouter) * (n : ℝ) ^ (-(a + 1)) := by
    calc
      cNorm * ‖banachTaylorCoefficient (F i) n‖ =
          ‖(2 * Real.pi * I) •
            banachTaylorCoefficient (F i) n‖ := by
        rw [norm_smul]
      _ = ‖banachCartesianLocalKeyhole (F i) M n +
          banachCartesianFixedOuterArcIntegral (F i) M n‖ := by
        rw [heq, norm_neg]
      _ ≤ ‖banachCartesianLocalKeyhole (F i) M n‖ +
          ‖banachCartesianFixedOuterArcIntegral (F i) M n‖ :=
        norm_add_le _ _
      _ ≤ Klocal * (n : ℝ) ^ (-(a + 1)) +
          Kouter * (n : ℝ) ^ (-(a + 1)) :=
        add_le_add (hnLocal i) (hnOuter i)
      _ = (Klocal + Kouter) * (n : ℝ) ^ (-(a + 1)) := by
        ring_nf
  calc
    ‖banachTaylorCoefficient (F i) n‖ ≤
        ((Klocal + Kouter) * (n : ℝ) ^ (-(a + 1))) / cNorm := by
      apply (le_div_iff₀ hcNorm).2
      simpa only [mul_comm] using hscaled
    _ = K * (n : ℝ) ^ (-(a + 1)) := by
      dsimp only [K]
      ring_nf

end PerronWright.Transfer
