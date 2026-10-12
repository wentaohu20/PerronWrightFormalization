import PerronWright.Probability.BrownianKilledAreaResolventBoundary
import PerronWright.Probability.BrownianKilledAreaResolventPolynomialMass

/-! # Finite target mass of actual all-order boundary insertions

Tonelli turns the true boundary insertion's total target mass into the
proved exponentially weighted initial-state moment mass. Thus the actual
boundary coefficients are integrable over the entire target state space.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianKilledAreaResolventBoundaryMass

open BrownianKilledAreaMomentResolvent BrownianKilledAreaResolventPolynomialMass

theorem measurable_boundary_insert (n : ℕ) (p : ℝ) :
    Measurable (fun y : ℝ ↦ ∫⁻ z : ℝ,
      ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*resolvent n p z y) := by
  have hg : Measurable (fun z : ℝ ↦ 2*Real.exp (-z*Real.sqrt (2*p))) :=
    measurable_const.mul ((measurable_id.neg.mul_const (Real.sqrt (2*p))).exp)
  have hm : Measurable (fun q : ℝ × ℝ ↦
      ENNReal.ofReal (2*Real.exp (-q.2*Real.sqrt (2*p)))*ENNReal.ofReal q.2*
        resolvent n p q.2 q.1) :=
    (((hg.comp measurable_snd).ennreal_ofReal).mul measurable_snd.ennreal_ofReal).mul
      ((measurable_resolvent n p).comp (measurable_snd.prodMk measurable_fst))
  exact hm.lintegral_prod_right'

theorem boundary_insert_total_mass_ne_top (n : ℕ) (p : ℝ) (hp : 0 < p) :
    (∫⁻ y : ℝ, ∫⁻ z : ℝ,
      ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*resolvent n p z y) ≠ ⊤ := by
  let s := Real.sqrt (2*p)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hg : Measurable (fun z : ℝ ↦ 2*Real.exp (-z*s)) :=
    measurable_const.mul ((measurable_id.neg.mul_const s).exp)
  have hm : Measurable (fun q : ℝ × ℝ ↦
      ENNReal.ofReal (2*Real.exp (-q.1*s))*ENNReal.ofReal q.1*resolvent n p q.1 q.2) :=
    (((hg.comp measurable_fst).ennreal_ofReal).mul measurable_fst.ennreal_ofReal).mul
      (measurable_resolvent n p)
  have he : (∫⁻ y : ℝ, ∫⁻ z : ℝ,
      ENNReal.ofReal (2*Real.exp (-z*s))*ENNReal.ofReal z*resolvent n p z y) =
      ENNReal.ofReal 2*(∫⁻ z : ℝ in Ioi 0, ENNReal.ofReal (z^(1 : ℝ)*Real.exp (-s*z))*
        ∫⁻ y : ℝ, resolvent n p z y) := by
    calc
      _ = ∫⁻ z : ℝ, ∫⁻ y : ℝ,
          ENNReal.ofReal (2*Real.exp (-z*s))*ENNReal.ofReal z*resolvent n p z y :=
        (lintegral_lintegral_swap hm.aemeasurable).symm
      _ = ∫⁻ z : ℝ, (ENNReal.ofReal (2*Real.exp (-z*s))*ENNReal.ofReal z)*
          ∫⁻ y : ℝ, resolvent n p z y := by
        apply lintegral_congr
        intro z
        exact lintegral_const_mul' _ _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      _ = _ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← lintegral_indicator measurableSet_Ioi]
        apply lintegral_congr
        intro z
        by_cases hz : 0 < z
        · rw [indicator_of_mem (show z ∈ Ioi (0 : ℝ) from hz),Real.rpow_one,
            ← ENNReal.ofReal_mul' hz.le,← mul_assoc,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 2
          rw [show -z*s = -s*z by ring]
          ac_rfl
        · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hz),mul_zero,zero_mul,
            indicator_of_notMem (show z ∉ Ioi (0 : ℝ) from hz)]
  change (∫⁻ y : ℝ, ∫⁻ z : ℝ,
    ENNReal.ofReal (2*Real.exp (-z*s))*ENNReal.ofReal z*resolvent n p z y) ≠ ⊤
  rw [he]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (exponential_weighted_total_mass_ne_top n p hp 1 (by norm_num) s hs)

theorem integrable_boundary_insert_real (n : ℕ) (p : ℝ) (hp : 0 < p) :
    Integrable (fun y : ℝ ↦ (∫⁻ z : ℝ,
      ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*resolvent n p z y).toReal)
      volume :=
  integrable_toReal_of_lintegral_ne_top (measurable_boundary_insert n p).aemeasurable
    (boundary_insert_total_mass_ne_top n p hp)

end PerronWright.BrownianKilledAreaResolventBoundaryMass
