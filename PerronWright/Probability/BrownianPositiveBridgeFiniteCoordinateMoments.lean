import PerronWright.Probability.BrownianPositiveBridgeAllTimeMoments
import Mathlib.Algebra.Order.Chebyshev

/-! # Genuine joint moment bounds at arbitrary finitely many times

The positive bridge is the actual conditional path law. Finite Jensen
and the proved all-time coordinate bounds control arbitrary powers of
one plus the sum of absolute coordinates, uniformly near zero endpoint.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeFiniteCoordinateMoments

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeAllTimeMoments

def radius {d : ℕ} (v : Fin d → ℝ) : ℝ := 1+∑ i, |v i|

theorem one_le_radius {d : ℕ} (v : Fin d → ℝ) : 1 ≤ radius v :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))

theorem continuous_radius (d : ℕ) : Continuous (radius (d := d)) := by
  unfold radius
  exact continuous_const.add (continuous_finsetSum _ (fun i _ ↦ (continuous_apply i).abs))

theorem coordinate_abs_le_radius {d : ℕ} (v : Fin d → ℝ) (i : Fin d) : |v i| ≤ radius v := by
  exact (Finset.single_le_sum (fun j _ ↦ abs_nonneg (v j)) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

theorem radius_pow_le_coordinate_sum {d : ℕ} (v : Fin d → ℝ) (k : ℕ) :
    radius v^k ≤ ((d+1 : ℕ) : ℝ)^(2*k+1)*(1+∑ i, |v i|^(2*k+2)) := by
  let w : Fin (d+1) → ℝ := Fin.cons 1 (fun i ↦ |v i|)
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin (d+1))), 0 ≤ w i := by
    intro i _
    refine Fin.cases (by norm_num [w]) (fun j ↦ ?_) i
    exact abs_nonneg _
  have hj := pow_sum_le_card_mul_sum_pow hw (2*k+1)
  have hs : (∑ i, w i) = radius v := by simp [w,Fin.sum_univ_succ,radius]
  have hp : (∑ i, w i^(2*k+2)) = 1+∑ i, |v i|^(2*k+2) := by
    simp [w,Fin.sum_univ_succ]
  rw [hs,hp] at hj
  calc
    _ ≤ radius v^(2*k+2) := pow_le_pow_right₀ (one_le_radius v) (by omega)
    _ ≤ _ := by simpa only [Finset.card_univ,Fintype.card_fin] using hj

def jointMomentBound (T : ℝ≥0) (d k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((d+1 : ℕ) : ℝ)^(2*k+1)) *
    (1+(d : ℝ≥0∞)*coordinateBound T (k+1))

theorem jointMomentBound_lt_top (T : ℝ≥0) (hT : 0 < T) (d k : ℕ) :
    jointMomentBound T d k < ∞ := by
  unfold jointMomentBound
  have := coordinateBound_lt_top T hT (k+1)
  finiteness

theorem eventually_uniform_finite_coordinate_moment (T : ℝ≥0) (hT : 0 < T) (d k : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ τ : Fin d → ℝ≥0, (∀ i, τ i ≤ T) →
      (∫⁻ g : Path, ENNReal.ofReal (radius (fun i ↦ g (τ i))^k) ∂positiveBridgeLaw a T) ≤
        jointMomentBound T d k := by
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_coordinate_moment_bound T hT (k+1)]
    with a ha hb
  let := positiveBridgeLaw_isProbability a ha T hT
  intro τ hτ
  have hm (i : Fin d) : Measurable (fun g : Path ↦ ENNReal.ofReal (|g (τ i)|^(2*k+2))) := by
    exact ((continuous_eval (τ i)).abs.pow _).measurable.ennreal_ofReal
  have hfun (g : Path) : ENNReal.ofReal (1+∑ i, |g (τ i)|^(2*k+2)) =
      1+∑ i, ENNReal.ofReal (|g (τ i)|^(2*k+2)) := by
    rw [ENNReal.ofReal_add (by norm_num) (Finset.sum_nonneg (fun _ _ ↦ by positivity)),
      ENNReal.ofReal_one,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
  have hs : (∫⁻ g : Path, 1+∑ i, ENNReal.ofReal (|g (τ i)|^(2*k+2)) ∂positiveBridgeLaw a T) ≤
      1+(d : ℝ≥0∞)*coordinateBound T (k+1) := by
    rw [lintegral_add_left measurable_const,lintegral_finsetSum _ (fun i _ ↦ hm i)]
    simp only [lintegral_const,measure_univ,mul_one]
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ _i : Fin d, coordinateBound T (k+1) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [show 2*(k+1) = 2*k+2 by omega] using hb (τ i) (hτ i)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ ∫⁻ g : Path, ENNReal.ofReal (((d+1 : ℕ) : ℝ)^(2*k+1))*
        (1+∑ i, ENNReal.ofReal (|g (τ i)|^(2*k+2))) ∂positiveBridgeLaw a T := by
      apply lintegral_mono
      intro g
      have he := ENNReal.ofReal_le_ofReal (radius_pow_le_coordinate_sum (fun i ↦ g (τ i)) k)
      rwa [ENNReal.ofReal_mul (by positivity),hfun] at he
    _ = ENNReal.ofReal (((d+1 : ℕ) : ℝ)^(2*k+1))*
        (∫⁻ g : Path, 1+∑ i, ENNReal.ofReal (|g (τ i)|^(2*k+2)) ∂positiveBridgeLaw a T) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl hs

theorem radius_tail_power_le_succ {d : ℕ} (v : Fin d → ℝ) (k : ℕ)
    {B : ℝ} (hB : 0 < B) (hv : B ≤ radius v) :
    ENNReal.ofReal (radius v^k) ≤ ENNReal.ofReal (radius v^(k+1))/ENNReal.ofReal B := by
  rw [← ENNReal.ofReal_div_of_pos hB]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ hB).mpr
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left hv (pow_nonneg (zero_le_one.trans (one_le_radius v)) k)

theorem eventually_uniform_finite_coordinate_tail_moment (T : ℝ≥0) (hT : 0 < T) (d k : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ τ : Fin d → ℝ≥0, (∀ i, τ i ≤ T) → ∀ B : ℝ, 0 < B →
      (∫⁻ g : Path in {g : Path | B ≤ radius (fun i ↦ g (τ i))},
        ENNReal.ofReal (radius (fun i ↦ g (τ i))^k) ∂positiveBridgeLaw a T) ≤
          jointMomentBound T d (k+1)/ENNReal.ofReal B := by
  filter_upwards [eventually_uniform_finite_coordinate_moment T hT d (k+1)] with a hb
  intro τ hτ B hB
  have hm : Measurable (fun g : Path ↦ radius (fun i ↦ g (τ i))) :=
    (continuous_radius d).measurable.comp (measurable_pi_lambda _ (fun i ↦ (continuous_eval (τ i)).measurable))
  calc
    _ ≤ ∫⁻ g : Path in {g : Path | B ≤ radius (fun i ↦ g (τ i))},
        ENNReal.ofReal (radius (fun i ↦ g (τ i))^(k+1))/ENNReal.ofReal B ∂positiveBridgeLaw a T := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_const hm)] with g hg
      exact radius_tail_power_le_succ _ k hB hg
    _ ≤ ∫⁻ g : Path, ENNReal.ofReal (radius (fun i ↦ g (τ i))^(k+1))/ENNReal.ofReal B ∂positiveBridgeLaw a T :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = (∫⁻ g : Path, ENNReal.ofReal (radius (fun i ↦ g (τ i))^(k+1)) ∂positiveBridgeLaw a T)/ENNReal.ofReal B := by
      simp only [div_eq_mul_inv]
      rw [lintegral_mul_const _ ((hm.pow_const (k+1)).ennreal_ofReal)]
    _ ≤ _ := ENNReal.div_le_div_right (hb τ hτ) _

theorem finite_coordinate_moment_tails_uniformly_vanish (T : ℝ≥0) (hT : 0 < T) (d k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ, 0 < a → a < δ →
      ∀ τ : Fin d → ℝ≥0, (∀ i, τ i ≤ T) →
        (∫⁻ g : Path in {g : Path | B ≤ radius (fun i ↦ g (τ i))},
          ENNReal.ofReal (radius (fun i ↦ g (τ i))^k) ∂positiveBridgeLaw a T) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ,hδ,hh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (eventually_uniform_finite_coordinate_tail_moment T hT d k)
  let C : ℝ := (jointMomentBound T d (k+1)).toReal
  let B : ℝ := C/ε+1
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hB : 0 < B := by dsimp [B]; positivity
  have hratio : C/B ≤ ε := by
    apply (div_le_iff₀ hB).mpr
    dsimp [B]
    rw [mul_add,mul_div_cancel₀ _ hε.ne',mul_one]
    exact le_add_of_nonneg_right hε.le
  have hENN : jointMomentBound T d (k+1)/ENNReal.ofReal B ≤ ENNReal.ofReal ε := by
    have he : jointMomentBound T d (k+1) = ENNReal.ofReal C :=
      (ENNReal.ofReal_toReal (jointMomentBound_lt_top T hT d (k+1)).ne).symm
    rw [he,← ENNReal.ofReal_div_of_pos hB]
    exact ENNReal.ofReal_le_ofReal hratio
  refine ⟨δ,hδ,B,hB,?_⟩
  intro a ha haδ τ hτ
  exact (hh ⟨ha,haδ⟩ τ hτ B hB).trans hENN

def monomial {d : ℕ} (p : Fin d → ℕ) (v : Fin d → ℝ) : ℝ := ∏ i, v i^(p i)

theorem continuous_monomial {d : ℕ} (p : Fin d → ℕ) : Continuous (monomial p) := by
  unfold monomial
  exact continuous_finsetProd _ (fun i _ ↦ (continuous_apply i).pow (p i))

theorem abs_monomial_le_radius_pow {d : ℕ} (p : Fin d → ℕ) (v : Fin d → ℝ) :
    |monomial p v| ≤ radius v^(∑ i, p i) := by
  unfold monomial
  rw [Finset.abs_prod]
  simp_rw [abs_pow]
  calc
    _ ≤ ∏ i : Fin d, radius v^(p i) := by
      apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
      intro i _
      exact pow_le_pow_left₀ (abs_nonneg _) (coordinate_abs_le_radius v i) _
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

def coordinatePolynomial {d m : ℕ} (c : Fin m → ℝ) (p : Fin m → Fin d → ℕ)
    (v : Fin d → ℝ) : ℝ := ∑ j, c j*monomial (p j) v

theorem continuous_coordinatePolynomial {d m : ℕ} (c : Fin m → ℝ) (p : Fin m → Fin d → ℕ) :
    Continuous (coordinatePolynomial c p) := by
  unfold coordinatePolynomial
  exact continuous_finsetSum _ (fun j _ ↦ (continuous_monomial (p j)).const_mul _)

theorem abs_coordinatePolynomial_le_radius_pow {d m : ℕ}
    (c : Fin m → ℝ) (p : Fin m → Fin d → ℕ) (v : Fin d → ℝ) :
    |coordinatePolynomial c p v| ≤ (∑ j, |c j|)*radius v^(∑ j, ∑ i, p j i) := by
  unfold coordinatePolynomial
  calc
    _ ≤ ∑ j, |c j*monomial (p j) v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |c j| * radius v^(∑ j, ∑ i, p j i) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (abs_monomial_le_radius_pow (p j) v).trans
        (pow_le_pow_right₀ (one_le_radius v)
          (Finset.single_le_sum (f := fun j : Fin m ↦ ∑ i, p j i)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)))
    _ = _ := by rw [Finset.sum_mul]

theorem abs_monomial_pow_le_radius_pow {d : ℕ} (p : Fin d → ℕ) (v : Fin d → ℝ) (l : ℕ) :
    |monomial p v|^l ≤ radius v^((∑ i, p i)*l) := by
  calc
    _ ≤ (radius v^(∑ i, p i))^l := pow_le_pow_left₀ (abs_nonneg _) (abs_monomial_le_radius_pow p v) l
    _ = _ := (pow_mul _ _ _).symm

theorem eventually_uniform_coordinate_monomial_moment (T : ℝ≥0) (hT : 0 < T) (d : ℕ)
    (p : Fin d → ℕ) (l : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ τ : Fin d → ℝ≥0, (∀ i, τ i ≤ T) →
      (∫⁻ g : Path, ENNReal.ofReal (|monomial p (fun i ↦ g (τ i))|^l) ∂positiveBridgeLaw a T) ≤
        jointMomentBound T d ((∑ i, p i)*l) := by
  filter_upwards [eventually_uniform_finite_coordinate_moment T hT d ((∑ i, p i)*l)] with a hb
  intro τ hτ
  exact (lintegral_mono (fun g ↦ ENNReal.ofReal_le_ofReal (abs_monomial_pow_le_radius_pow p _ l))).trans (hb τ hτ)

theorem coordinate_monomial_moment_tails_uniformly_vanish (T : ℝ≥0) (hT : 0 < T) (d : ℕ)
    (p : Fin d → ℕ) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 < a → a < δ →
      ∀ τ : Fin d → ℝ≥0, (∀ i, τ i ≤ T) →
        (∫⁻ g : Path in {g : Path | K ≤ |monomial p (fun i ↦ g (τ i))|^l},
          ENNReal.ofReal (|monomial p (fun i ↦ g (τ i))|^l) ∂positiveBridgeLaw a T) ≤ ENNReal.ofReal ε := by
  let D := (∑ i, p i)*l
  obtain ⟨δ,hδ,B,hB,hh⟩ := finite_coordinate_moment_tails_uniformly_vanish T hT d D hε
  let K := B^D+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨δ,hδ,K,hK,?_⟩
  intro a ha haδ τ hτ
  have hsub : {g : Path | K ≤ |monomial p (fun i ↦ g (τ i))|^l} ⊆
      {g : Path | B ≤ radius (fun i ↦ g (τ i))} := by
    intro g hg
    by_contra hn
    have hr : radius (fun i ↦ g (τ i)) ≤ B := (lt_of_not_ge hn).le
    have hp := (abs_monomial_pow_le_radius_pow p (fun i ↦ g (τ i)) l).trans
      (pow_le_pow_left₀ (zero_le_one.trans (one_le_radius _)) hr D)
    change B^D+1 ≤ |monomial p (fun i ↦ g (τ i))|^l at hg
    linarith
  calc
    _ ≤ ∫⁻ g : Path in {g : Path | K ≤ |monomial p (fun i ↦ g (τ i))|^l},
        ENNReal.ofReal (radius (fun i ↦ g (τ i))^D) ∂positiveBridgeLaw a T :=
      lintegral_mono (fun g ↦ ENNReal.ofReal_le_ofReal (abs_monomial_pow_le_radius_pow p _ l))
    _ ≤ ∫⁻ g : Path in {g : Path | B ≤ radius (fun i ↦ g (τ i))},
        ENNReal.ofReal (radius (fun i ↦ g (τ i))^D) ∂positiveBridgeLaw a T := lintegral_mono_set hsub
    _ ≤ _ := hh a ha haδ τ hτ

theorem abs_coordinatePolynomial_pow_le_radius_pow {d m : ℕ}
    (c : Fin m → ℝ) (p : Fin m → Fin d → ℕ) (v : Fin d → ℝ) (l : ℕ) :
    |coordinatePolynomial c p v|^l ≤ (∑ j, |c j|)^l*radius v^((∑ j, ∑ i, p j i)*l) := by
  calc
    _ ≤ ((∑ j, |c j|)*radius v^(∑ j, ∑ i, p j i))^l :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_coordinatePolynomial_le_radius_pow c p v) l
    _ = _ := by rw [mul_pow,← pow_mul]

theorem eventually_uniform_coordinatePolynomial_moment (T : ℝ≥0) (hT : 0 < T)
    (d m : ℕ) (c : Fin m → ℝ) (p : Fin m → Fin d → ℕ) (l : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ τ : Fin d → ℝ≥0, (∀ i, τ i ≤ T) →
      (∫⁻ g : Path, ENNReal.ofReal (|coordinatePolynomial c p (fun i ↦ g (τ i))|^l) ∂positiveBridgeLaw a T) ≤
        ENNReal.ofReal ((∑ j, |c j|)^l)*jointMomentBound T d ((∑ j, ∑ i, p j i)*l) := by
  let D := (∑ j, ∑ i, p j i)*l
  have hC : 0 ≤ (∑ j, |c j|)^l := pow_nonneg (Finset.sum_nonneg (fun j _ ↦ abs_nonneg (c j))) l
  filter_upwards [eventually_uniform_finite_coordinate_moment T hT d D] with a hb
  intro τ hτ
  calc
    _ ≤ ∫⁻ g : Path, ENNReal.ofReal ((∑ j, |c j|)^l)*
        ENNReal.ofReal (radius (fun i ↦ g (τ i))^D) ∂positiveBridgeLaw a T := by
      apply lintegral_mono
      intro g
      dsimp only
      rw [← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (abs_coordinatePolynomial_pow_le_radius_pow c p _ l)
    _ = ENNReal.ofReal ((∑ j, |c j|)^l)*
        (∫⁻ g : Path, ENNReal.ofReal (radius (fun i ↦ g (τ i))^D) ∂positiveBridgeLaw a T) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (hb τ hτ)

theorem coordinatePolynomial_moment_tails_uniformly_vanish (T : ℝ≥0) (hT : 0 < T)
    (d m : ℕ) (c : Fin m → ℝ) (p : Fin m → Fin d → ℕ) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 < a → a < δ →
      ∀ τ : Fin d → ℝ≥0, (∀ i, τ i ≤ T) →
        (∫⁻ g : Path in {g : Path | K ≤ |coordinatePolynomial c p (fun i ↦ g (τ i))|^l},
          ENNReal.ofReal (|coordinatePolynomial c p (fun i ↦ g (τ i))|^l) ∂positiveBridgeLaw a T) ≤ ENNReal.ofReal ε := by
  let D := (∑ j, ∑ i, p j i)*l
  let C := (∑ j, |c j|)^l
  have hC : 0 ≤ C := pow_nonneg (Finset.sum_nonneg (fun j _ ↦ abs_nonneg (c j))) l
  have hCp : 0 < C+1 := by linarith
  have heps : 0 < ε/(C+1) := div_pos hε hCp
  obtain ⟨δ,hδ,B,hB,hh⟩ := finite_coordinate_moment_tails_uniformly_vanish T hT d D heps
  let K := C*B^D+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hscale : ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hCp).mpr
    nlinarith
  refine ⟨δ,hδ,K,hK,?_⟩
  intro a ha haδ τ hτ
  have hsub : {g : Path | K ≤ |coordinatePolynomial c p (fun i ↦ g (τ i))|^l} ⊆
      {g : Path | B ≤ radius (fun i ↦ g (τ i))} := by
    intro g hg
    by_contra hn
    have hr : radius (fun i ↦ g (τ i)) ≤ B := (lt_of_not_ge hn).le
    have hp := (abs_coordinatePolynomial_pow_le_radius_pow c p (fun i ↦ g (τ i)) l).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (one_le_radius _)) hr D) hC)
    change C*B^D+1 ≤ |coordinatePolynomial c p (fun i ↦ g (τ i))|^l at hg
    linarith
  calc
    _ ≤ ∫⁻ g : Path in {g : Path | K ≤ |coordinatePolynomial c p (fun i ↦ g (τ i))|^l},
        ENNReal.ofReal C*ENNReal.ofReal (radius (fun i ↦ g (τ i))^D) ∂positiveBridgeLaw a T := by
      apply lintegral_mono
      intro g
      dsimp only
      rw [← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (abs_coordinatePolynomial_pow_le_radius_pow c p _ l)
    _ ≤ ∫⁻ g : Path in {g : Path | B ≤ radius (fun i ↦ g (τ i))},
        ENNReal.ofReal C*ENNReal.ofReal (radius (fun i ↦ g (τ i))^D) ∂positiveBridgeLaw a T := lintegral_mono_set hsub
    _ = ENNReal.ofReal C*(∫⁻ g : Path in {g : Path | B ≤ radius (fun i ↦ g (τ i))},
        ENNReal.ofReal (radius (fun i ↦ g (τ i))^D) ∂positiveBridgeLaw a T) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) := mul_le_mul' le_rfl (hh a ha haδ τ hτ)
    _ ≤ _ := hscale

end PerronWright.BrownianPositiveBridgeFiniteCoordinateMoments
