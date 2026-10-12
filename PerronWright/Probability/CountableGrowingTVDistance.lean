import PerronWright.Probability.CountableTVDistanceRequirements
import PerronWright.Probability.CountableFixedSupportGrowingLocalMain

/-! # TV-profile collapse for the actual growing rounded source

Distance to the retained Perron mark is forced by genuine fixed-support
requirements. The actual retained marks converge in atomic variation;
the finite tuple triangle inequality then gives collapse to the original
countable Perron mark, on the same local-main realization.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open CountableVariationMarks

def growingDistanceLocalExpectation (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (n : ℕ) (y : Fin 1 → ℝ) (r : Fin 1 → ℕ) (p : VariationMark) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
    ∫ G, CountableVariationComponentCounts.markedCount
      (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G
      (fun i ↦ CriticalScaling.size (y i) (n + 1)) r (distanceTest p)
      ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n

theorem growingDistanceLocalExpectation_nonneg
    (M : CountableKernel) (level : ℕ → ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (n : ℕ) (y : Fin 1 → ℝ) (r : Fin 1 → ℕ) (p : VariationMark) :
    0 ≤ M.growingDistanceLocalExpectation level lambda hlower hlo n y r p := by
  apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
  exact integral_nonneg (fun _ ↦ CountableVariationComponentCounts.markedCount_distance_nonneg _ _ _ _ _)

theorem growingDistanceLocalExpectation_eq_fixedSupport
    (M : CountableKernel) (level : ℕ → ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (n : ℕ) (y : Fin 1 → ℝ) (r : Fin 1 → ℕ) :
    M.growingDistanceLocalExpectation level lambda hlower hlo n y r
      (M.fixedSupportPerronMark (level (n + 1)) hlower hlo) =
    M.fixedSupportDistanceLocalExpectation (level (n + 1)) lambda hlower hlo n y r := by
  unfold growingDistanceLocalExpectation fixedSupportDistanceLocalExpectation
  rw [M.empiricalNormalizedGraphLaw_eq_fixedSupport_level level lambda hlower hlo n]

theorem growingDistanceLocalExpectation_triangle
    (M : CountableKernel) (level : ℕ → ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (n : ℕ) (y : Fin 1 → ℝ) (r : Fin 1 → ℕ) (p q : VariationMark) :
    M.growingDistanceLocalExpectation level lambda hlower hlo n y r p ≤
      M.growingDistanceLocalExpectation level lambda hlower hlo n y r q +
        dist q p * M.growingLocalExpectation level lambda hlower hlo n y r := by
  have hi := integral_mono (μ := M.empiricalNormalizedGraphLaw level lambda hlower hlo n)
    (Integrable.of_finite) (Integrable.of_finite)
    (fun G ↦ CountableVariationComponentCounts.markedCount_distance_triangle
      (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G
      (fun i ↦ CriticalScaling.size (y i) (n + 1)) r p q)
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul] at hi
  have hh := mul_le_mul_of_nonneg_left hi
    (Real.rpow_nonneg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)) (2 / 3 : ℝ))
  simpa only [growingDistanceLocalExpectation, growingLocalExpectation,
    Nat.cast_one, mul_one, mul_add, mul_assoc, mul_left_comm] using hh

private theorem exists_distance_window_index (R : ℕ) (a b L ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ j : ℕ, R ≤ j + 1 ∧ L ≤ (j + 1 : ℝ) ∧ b ≤ (j + 1 : ℝ) ∧
      1 / (j + 1 : ℝ) ≤ a ∧ 1 / (j + 1 : ℝ) < ε := by
  have ht : Tendsto (fun j : ℕ ↦ (j + 1 : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv := ht.inv_tendsto_atTop
  have he : ∀ᶠ j : ℕ in atTop,
      R ≤ j + 1 ∧ L ≤ (j + 1 : ℝ) ∧ b ≤ (j + 1 : ℝ) ∧
        1 / (j + 1 : ℝ) ≤ a ∧ 1 / (j + 1 : ℝ) < ε := by
    filter_upwards [eventually_ge_atTop R, ht.eventually_ge_atTop L, ht.eventually_ge_atTop b,
      hinv.eventually (Iio_mem_nhds ha), hinv.eventually (Iio_mem_nhds hε)]
      with j hR hL hb hja hje
    exact ⟨by omega, hL, hb, (by simpa only [one_div, Pi.inv_apply] using hja.le),
      (by simpa only [one_div, Pi.inv_apply] using hje)⟩
  exact he.exists

theorem growing_retained_distance_zero_of_actual_requirements
    (M : CountableKernel) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (level : ℕ → ℕ)
    (hdiag : ∀ j, ∀ᶠ N in atTop, M.fixedSupportTVDistanceRequirement hlower hlo (level N) j N)
    (R : ℕ) (a b L : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      M.growingDistanceLocalExpectation level lambda hlower hlo n y r
        (M.fixedSupportPerronMark (level (n + 1)) hlower hlo) < ε := by
  obtain ⟨j, hRj, hLj, hbj, haj, hej⟩ := exists_distance_window_index R a b L ε ha hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (hdiag j)]
    with n hn lambda hl y r hya hyb hr
  rw [M.growingDistanceLocalExpectation_eq_fixedSupport level lambda hlower hlo n y r]
  exact (hn lambda (hl.trans hLj) y r (fun i ↦ haj.trans (hya i))
    (fun i ↦ (hyb i).trans hbj) (fun i ↦ (hr i).trans hRj)).trans hej

theorem growing_perron_distance_zero_of_actual_requirements
    (M : CountableKernel) (hM : M.IsRegularCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (level : ℕ → ℕ) (ht : Tendsto level atTop atTop)
    (hlocal : ∀ j, ∀ᶠ N in atTop, M.fixedSupportLocalRequirement hlower hlo (level N) j N)
    (hTV : ∀ j, ∀ᶠ N in atTop, M.fixedSupportTVDistanceRequirement hlower hlo (level N) j N)
    (R : ℕ) (a b L : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      M.growingDistanceLocalExpectation level lambda hlower hlo n y r
        (CountablePerronMarkConvergence.perronMark M hM) < ε := by
  obtain ⟨C, hC, hbound⟩ := FactorialDensity.exists_density_window_bound
    (b := b) (M.beta_pos hM) ha R
  let B := C * Real.exp (-M.beta hM * a ^ 3 / 24)
  have hB : 0 < B := mul_pos hC (Real.exp_pos _)
  have hp := (tendsto_iff_dist_tendsto_zero.mp (M.fixedSupportPerronMark_tendsto hM hlower hlo)).comp
    (ht.comp (tendsto_add_atTop_nat 1))
  filter_upwards [M.growing_retained_distance_zero_of_actual_requirements hlower hlo level hTV
      R a b L ha (show 0 < ε / 2 by positivity),
    M.growing_local_main_of_actual_requirements hM hlower hlo level ht hlocal 1 R (by norm_num)
      a b L ha (show 0 < (1 : ℝ) by norm_num),
    hp.eventually (Iio_mem_nhds (show 0 < ε / (2 * (B + 1)) by positivity))]
    with n hret hmain hdist lambda hl y r hya hyb hr
  have he := hmain lambda hl y r hya hyb hr
  have hd := hbound 1 (M.alpha hM) lambda y r (fun i ↦ ⟨hya i, hyb i⟩) hr
  have hval : M.growingLocalExpectation level lambda hlower hlo n y r ≤ B + 1 := by
    have hh := (abs_sub_lt_iff.mp he).1
    norm_num only [Nat.cast_one, pow_one, mul_one] at hd
    dsimp only [B]
    linarith
  have hprod : dist (M.fixedSupportPerronMark (level (n + 1)) hlower hlo)
      (CountablePerronMarkConvergence.perronMark M hM) *
      M.growingLocalExpectation level lambda hlower hlo n y r < ε / 2 := by
    calc
      _ ≤ dist (M.fixedSupportPerronMark (level (n + 1)) hlower hlo)
          (CountablePerronMarkConvergence.perronMark M hM) * (B + 1) :=
        mul_le_mul_of_nonneg_left hval dist_nonneg
      _ < (ε / (2 * (B + 1))) * (B + 1) :=
        mul_lt_mul_of_pos_right hdist (by positivity)
      _ = ε / 2 := by field_simp
  exact (M.growingDistanceLocalExpectation_triangle level lambda hlower hlo n y r
    (CountablePerronMarkConvergence.perronMark M hM)
    (M.fixedSupportPerronMark (level (n + 1)) hlower hlo)).trans_lt
      (by linarith [hret lambda hl y r hya hyb hr])

end PerronWright.CountableKernel
