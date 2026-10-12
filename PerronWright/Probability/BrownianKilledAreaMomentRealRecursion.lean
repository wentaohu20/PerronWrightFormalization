import PerronWright.Probability.BrownianKilledAreaMomentRealKernel
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Finite real Kac insertions of the actual killed area moments

Finiteness is a conclusion about the Brownian source. The time-insertion
integrals are integrable consequences of its proved ENN recursion, not
additional moment or Kac premises.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentRealRecursion

open BrownianKilledAreaMomentKernel BrownianKilledAreaMomentFiniteness
open BrownianKilledAreaMomentRealKernel BrownianKilledAreaMomentRecursion
open BrownianKilledSemigroup BrownianKilledAreaDuhamelGeometry

def insertionMass (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    (F : ℝ → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (z-level) *
    (∫⁻ y, F y ∂momentLaw level n (T-Real.toNNReal s) z)
      ∂transitionLaw level (Real.toNNReal s) x

theorem measurable_insertionMass (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) : Measurable (insertionMass level n T x F) := by
  let κ : Kernel ℝ ℝ := (timeMomentKernel level 0).comap
    (fun s : ℝ ↦ (Real.toNNReal s,x))
    (continuous_real_toNNReal.measurable.prodMk measurable_const)
  have hg : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.2-level) *
      (∫⁻ y, F y ∂momentLaw level n (T-Real.toNNReal p.1) p.2)) :=
    (measurable_snd.sub_const level).ennreal_ofReal.mul
      ((measurable_time_state_momentLaw_lintegral level n hF).comp
        ((measurable_const.sub (continuous_real_toNNReal.measurable.comp measurable_fst)).prodMk
          measurable_snd))
  have hm := hg.lintegral_kernel_prod_right' (κ := κ)
  unfold insertionMass
  simpa only [κ,Kernel.comap_apply,timeMomentKernel_apply,momentLaw_zero] using hm

theorem lintegral_bounded_test_ne_top (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    (∫⁻ y, ENNReal.ofReal (F y) ∂momentLaw level n T x) ≠ ∞ := by
  apply (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal (momentLaw level n T x) _).ne
  refine ⟨Real.toNNReal C,fun y ↦ ?_⟩
  change ENNReal.ofReal (F y) ≤ ENNReal.ofReal C
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC y))

theorem lintegral_insertionMass_ne_top (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    (∫⁻ s in Ioc (0 : ℝ) (T : ℝ), insertionMass level n T x (fun y ↦ ENNReal.ofReal (F y)) s) ≠ ∞ := by
  have h := momentLaw_lintegral_insertion level T x n hF.ennreal_ofReal
  have hfin := lintegral_bounded_test_ne_top level (n+1) T x hC
  rw [h] at hfin
  exact (ENNReal.lt_top_of_mul_ne_top_right hfin (by simp)).ne

def realInsertion (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ z, max (z-level) 0 * (∫ y, F y ∂momentLaw level n (T-Real.toNNReal s) z)
      ∂transitionLaw level (Real.toNNReal s) x

theorem realInsertion_eq_toReal (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) (hF0 : ∀ y, 0 ≤ F y)
    {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) (s : ℝ) :
    realInsertion level n T x F s =
      (insertionMass level n T x (fun y ↦ ENNReal.ofReal (F y)) s).toReal := by
  have hm : Measurable (fun z : ℝ ↦ ENNReal.ofReal (z-level) *
      (∫⁻ y, ENNReal.ofReal (F y) ∂momentLaw level n (T-Real.toNNReal s) z)) :=
    (measurable_id.sub_const level).ennreal_ofReal.mul
      (measurable_momentLaw_lintegral level n _ hF.ennreal_ofReal)
  have hf (z : ℝ) : ENNReal.ofReal (z-level) *
      (∫⁻ y, ENNReal.ofReal (F y) ∂momentLaw level n (T-Real.toNNReal s) z) < ∞ :=
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_bounded_test_ne_top level n _ z hC)).lt_top
  unfold realInsertion insertionMass
  rw [← integral_toReal hm.aemeasurable (Eventually.of_forall hf)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z ↦ by
    dsimp only
    rw [ENNReal.toReal_mul,integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall hF0) hF.aestronglyMeasurable,ENNReal.toReal_ofReal'])

theorem integrable_realInsertion_nonneg (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) (hF0 : ∀ y, 0 ≤ F y)
    {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    IntegrableOn (realInsertion level n T x F) (Ioc (0 : ℝ) (T : ℝ)) := by
  have he := funext (realInsertion_eq_toReal level n T x hF hF0 hC)
  rw [he]
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_insertionMass level n T x hF.ennreal_ofReal).aemeasurable
    (lintegral_insertionMass_ne_top level n T x hF hC)

theorem momentLaw_integral_insertion_nonneg (level : ℝ) (T : ℝ≥0) (x : ℝ) (n : ℕ)
    {F : ℝ → ℝ} (hF : Measurable F) (hF0 : ∀ y, 0 ≤ F y)
    {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    (∫ y, F y ∂momentLaw level (n+1) T x) =
      (n+1 : ℝ) * ∫ s in Ioc (0 : ℝ) (T : ℝ), realInsertion level n T x F s := by
  have hm := measurable_insertionMass level n T x hF.ennreal_ofReal
  have hi := lintegral_insertionMass_ne_top level n T x hF hC
  have he := funext (realInsertion_eq_toReal level n T x hF hF0 hC)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hF.aestronglyMeasurable,
    momentLaw_lintegral_insertion level T x n hF.ennreal_ofReal,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,he,
    integral_toReal hm.aemeasurable (ae_lt_top hm hi)]
  simp only [Nat.cast_add,Nat.cast_one]
  rfl

theorem integrable_stateInsertion_ae_nonneg (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) (hF0 : ∀ y, 0 ≤ F y)
    {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      Integrable (fun z ↦ max (z-level) 0 *
        (∫ y, F y ∂momentLaw level n (T-Real.toNNReal s) z))
          (transitionLaw level (Real.toNNReal s) x) := by
  have hm := measurable_insertionMass level n T x hF.ennreal_ofReal
  have hi := lintegral_insertionMass_ne_top level n T x hF hC
  filter_upwards [ae_lt_top hm hi] with s hs
  have hg : Measurable (fun z : ℝ ↦ ENNReal.ofReal (z-level) *
      (∫⁻ y, ENNReal.ofReal (F y) ∂momentLaw level n (T-Real.toNNReal s) z)) :=
    (measurable_id.sub_const level).ennreal_ofReal.mul
      (measurable_momentLaw_lintegral level n _ hF.ennreal_ofReal)
  have h := integrable_toReal_of_lintegral_ne_top hg.aemeasurable hs.ne
  convert h using 1
  funext z
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal',integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall hF0) hF.aestronglyMeasurable]

private theorem bounded_posPart {F : ℝ → ℝ} {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    ∀ y, ‖max (F y) 0‖ ≤ C := by
  intro y
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC y))
    ((norm_nonneg (F y)).trans (hC y))

private theorem realInsertion_sub_ae (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {P N : ℝ → ℝ} (hP : Measurable P) (hN : Measurable N)
    (hP0 : ∀ y, 0 ≤ P y) (hN0 : ∀ y, 0 ≤ N y)
    {C : ℝ} (hPC : ∀ y, ‖P y‖ ≤ C) (hNC : ∀ y, ‖N y‖ ≤ C) :
    realInsertion level n T x (fun y ↦ P y-N y) =ᵐ[volume.restrict (Ioc (0 : ℝ) (T : ℝ))]
      (fun s ↦ realInsertion level n T x P s-realInsertion level n T x N s) := by
  filter_upwards [integrable_stateInsertion_ae_nonneg level n T x hP hP0 hPC,
    integrable_stateInsertion_ae_nonneg level n T x hN hN0 hNC] with s hsP hsN
  unfold realInsertion
  have he : (fun z ↦ max (z-level) 0 *
      (∫ y, P y-N y ∂momentLaw level n (T-Real.toNNReal s) z)) =
      fun z ↦ max (z-level) 0 * (∫ y, P y ∂momentLaw level n (T-Real.toNNReal s) z) -
        max (z-level) 0 * (∫ y, N y ∂momentLaw level n (T-Real.toNNReal s) z) := by
    funext z
    rw [integral_sub (integrable_bounded_endpoint_test level n _ z hP hPC)
      (integrable_bounded_endpoint_test level n _ z hN hNC),mul_sub]
  rw [he,integral_sub hsP hsN]

theorem integrable_realInsertion (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    IntegrableOn (realInsertion level n T x F) (Ioc (0 : ℝ) (T : ℝ)) := by
  have hNC : ∀ y, ‖-F y‖ ≤ C := fun y ↦ by simpa only [norm_neg] using hC y
  have hi := (integrable_realInsertion_nonneg level n T x (hF.max measurable_const)
    (fun y ↦ le_max_right (F y) 0) (bounded_posPart hC)).sub
    (integrable_realInsertion_nonneg level n T x (hF.neg.max measurable_const)
      (fun y ↦ le_max_right (-F y) 0) (bounded_posPart hNC))
  have hae := realInsertion_sub_ae level n T x (hF.max measurable_const)
    (hF.neg.max measurable_const) (fun y ↦ le_max_right (F y) 0)
    (fun y ↦ le_max_right (-F y) 0) (bounded_posPart hC) (bounded_posPart hNC)
  have he : (fun y ↦ max (F y) 0-max (-F y) 0) = F :=
    funext (fun y ↦ max_zero_sub_eq_self (F y))
  simp only [Pi.neg_apply] at hae
  rw [he] at hae
  exact hi.congr hae.symm

/-- Ordinary signed Bochner Kac formula for every bounded Borel endpoint
test. Both the surviving moment measure and the time integral are finite
conclusions about the actual Brownian source. -/
theorem momentLaw_integral_insertion (level : ℝ) (T : ℝ≥0) (x : ℝ) (n : ℕ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    (∫ y, F y ∂momentLaw level (n+1) T x) =
      (n+1 : ℝ) * ∫ s in Ioc (0 : ℝ) (T : ℝ), realInsertion level n T x F s := by
  have hNC : ∀ y, ‖-F y‖ ≤ C := fun y ↦ by simpa only [norm_neg] using hC y
  have hP : Measurable (fun y ↦ max (F y) 0) := hF.max measurable_const
  have hN : Measurable (fun y ↦ max (-F y) 0) := hF.neg.max measurable_const
  have hPC := bounded_posPart hC
  have hNC' := bounded_posPart hNC
  have hP0 := fun y ↦ le_max_right (F y) 0
  have hN0 := fun y ↦ le_max_right (-F y) 0
  have he : (fun y ↦ max (F y) 0-max (-F y) 0) = F :=
    funext (fun y ↦ max_zero_sub_eq_self (F y))
  have hae := realInsertion_sub_ae level n T x hP hN hP0 hN0 hPC hNC'
  rw [he] at hae
  have hleft : (∫ y, F y ∂momentLaw level (n+1) T x) =
      (∫ y, max (F y) 0 ∂momentLaw level (n+1) T x) -
        ∫ y, max (-F y) 0 ∂momentLaw level (n+1) T x := by
    rw [← integral_sub (integrable_bounded_endpoint_test level (n+1) T x hP hPC)
      (integrable_bounded_endpoint_test level (n+1) T x hN hNC'),he]
  rw [hleft,momentLaw_integral_insertion_nonneg level T x n hP hP0 hPC,
    momentLaw_integral_insertion_nonneg level T x n hN hN0 hNC',
    integral_congr_ae hae,
    integral_sub (integrable_realInsertion_nonneg level n T x hP hP0 hPC)
      (integrable_realInsertion_nonneg level n T x hN hN0 hNC'),mul_sub]

end PerronWright.BrownianKilledAreaMomentRealRecursion
