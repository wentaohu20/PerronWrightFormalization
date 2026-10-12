import PerronWright.Probability.CountableTVWindowProfile
import PerronWright.Probability.CountableGrowingTVLocalTerminal

/-! # Actual whole-window TV distance from the proved local error

The exact integer fibre sum has at most scaled window width plus one
size indices. Thus a uniform scaled first-order distance error gives an
actual entire-window expectation error. No point-process limit or
mark-space compactness is used in this finite-grid argument.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableTVWindowProfile

open CountableVariationMarks ComponentWindowPointMeasures ComponentWindowFactorialCounts

theorem integerWindow_card_le (d a b : ℝ) (hd : 0 < d) (ha : 0 ≤ a) (hab : a ≤ b) :
    ((integerWindow d (fun _ : Fin 1 ↦ a) (fun _ ↦ b)).card : ℝ) ≤ (b - a) * d + 1 := by
  have hceil : ⌈a * d⌉₊ ≤ ⌊b * d⌋₊ + 1 :=
    (Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right hab hd.le)).trans (Nat.ceil_le_floor_add_one _)
  have hfloor : (⌊b * d⌋₊ : ℝ) ≤ b * d := Nat.floor_le (mul_nonneg (ha.trans hab) hd.le)
  have hc : a * d ≤ (⌈a * d⌉₊ : ℝ) := Nat.le_ceil _
  simp only [integerWindow, Pi.card_Icc, Fin.prod_univ_one, Nat.card_Icc]
  rw [Nat.cast_sub hceil]
  push_cast
  nlinarith

theorem windowDistance_expectation_eq_integer_sum {n : ℕ} (x : Fin n → ℕ)
    (hn : 0 < n) (a b : ℝ) (hb : 0 ≤ b) (R : ℕ) (p : VariationMark)
    (μ : Measure (SimpleGraph (Fin n))) [IsFiniteMeasure μ] :
    (∫ G, windowDistance x G a b R p ∂μ) =
      ∑ r ∈ surplusIndices 1 R,
        ∑ k ∈ integerWindow ((n : ℝ) ^ (2 / 3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b),
          ∫ G, CountableVariationComponentCounts.markedCount x G k r (distanceTest p) ∂μ := by
  simp_rw [windowDistance_eq_integer_sum x _ hn a b hb R p]
  rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro r _
  exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)

theorem windowDistance_expectation_le_of_scaled {n : ℕ} (x : Fin n → ℕ)
    (hn : 0 < n) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (R : ℕ) (p : VariationMark)
    (μ : Measure (SimpleGraph (Fin n))) [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      (n : ℝ) ^ (2 / 3 : ℝ) *
        (∫ G, CountableVariationComponentCounts.markedCount x G
          (fun i ↦ CriticalScaling.size (y i) n) r (distanceTest p) ∂μ) ≤ ε) :
    (∫ G, windowDistance x G a b R p ∂μ) ≤ (R + 1 : ℝ) * (b - a + 1) * ε := by
  let d := (n : ℝ) ^ (2 / 3 : ℝ)
  have hd : 0 < d := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hd1 : 1 ≤ d := Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  let K := integerWindow d (fun _ : Fin 1 ↦ a) (fun _ ↦ b)
  let L := surplusIndices 1 R
  have hki {k : Fin 1 → ℕ} (hk : k ∈ K) (r : Fin 1 → ℕ) (hr : r ∈ L) :
      (∫ G, CountableVariationComponentCounts.markedCount x G k r (distanceTest p) ∂μ) ≤ ε / d := by
    have hy := (mem_integerWindow hd (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ ha.trans hab)).mp hk
    have he := hlocal (fun i ↦ (k i : ℝ) / d) r (fun i ↦ (hy i).1) (fun i ↦ (hy i).2)
      (mem_surplusIndices.mp hr)
    have hf : (fun i ↦ CriticalScaling.size ((k i : ℝ) / d) n) = k := by
      funext i
      simp only [CriticalScaling.size]
      rw [show (n : ℝ) ^ (2 / 3 : ℝ) = d from rfl, div_mul_cancel₀ _ hd.ne', Nat.floor_natCast]
    rw [hf] at he
    exact (le_div_iff₀ hd).mpr (by simpa only [d, mul_comm] using he)
  have hcard : (K.card : ℝ) ≤ (b - a + 1) * d := by
    have hh := integerWindow_card_le d a b hd ha hab
    change (K.card : ℝ) ≤ (b - a) * d + 1 at hh
    nlinarith
  have hL : L.card = R + 1 := by simp [L, surplusIndices, Pi.card_Icc]
  rw [windowDistance_expectation_eq_integer_sum x hn a b (ha.trans hab) R p μ]
  calc
    _ ≤ ∑ r ∈ L, ∑ _k ∈ K, ε / d := Finset.sum_le_sum (fun r hr ↦
      Finset.sum_le_sum (fun k hk ↦ hki hk r hr))
    _ = (L.card : ℝ) * ((K.card : ℝ) * (ε / d)) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L.card : ℝ) * (((b - a + 1) * d) * (ε / d)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard (div_nonneg hε hd.le))
        (Nat.cast_nonneg _)
    _ = (R + 1 : ℝ) * (b - a + 1) * ε := by rw [hL]; push_cast; field_simp

end PerronWright.CountableTVWindowProfile

namespace PerronWright.CountableKernel

open CountableVariationMarks CountableTVWindowProfile

def growingWindowDistanceExpectation (M : CountableKernel) (level : ℕ → ℕ)
    (lambda a b : ℝ) (R : ℕ) {lower : ℝ} (hlower : 0 < lower)
    (hlo : ∀ s t, lower ≤ M.kernel s t) (n : ℕ) (p : VariationMark) : ℝ :=
  ∫ G, windowDistance (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1))
    G a b R p ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n

theorem growing_windowDistance_zero_of_local_distance
    (M : CountableKernel) (level : ℕ → ℕ) (p : VariationMark)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hTV : ∀ R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      M.growingDistanceLocalExpectation level lambda hlower hlo n y r p < ε)
    (a b L : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      M.growingWindowDistanceExpectation level lambda a b R hlower hlo n p < ε := by
  let W := (R + 1 : ℝ) * (b - a + 1)
  have hW : 0 < W := mul_pos (by positivity) (by linarith)
  let η := ε / (W + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  filter_upwards [hTV R a b L ha η hη] with n hn lambda hl
  have he := windowDistance_expectation_le_of_scaled
    (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) (Nat.succ_pos n)
    a b ha.le hab R p (M.empiricalNormalizedGraphLaw level lambda hlower hlo n) η hη.le
    (fun y r hya hyb hr ↦ (hn lambda hl y r hya hyb hr).le)
  change M.growingWindowDistanceExpectation level lambda a b R hlower hlo n p ≤ W * η at he
  apply he.trans_lt
  dsimp only [η]
  have hh : W < W + 1 := by linarith
  exact (mul_div_assoc W ε (W + 1)).symm ▸
    (by exact (div_lt_iff₀ (by positivity : 0 < W + 1)).mpr (by nlinarith))

end PerronWright.CountableKernel
