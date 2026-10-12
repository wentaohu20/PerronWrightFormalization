import PerronWright.CyclePrimitive
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace PerronWright.KernelCycle

variable {S : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

def coeff (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ)) : ℕ → ℂ :=
  fun m => if 2 ≤ m then
    (cycleTrace mu a (m - 1) : ℂ) / (((2 : ℝ) * m) : ℂ)
  else 0

omit [BorelSpace S] in
@[simp] lemma coeff_zero (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ)) :
    coeff mu a 0 = 0 := by simp [coeff]
omit [BorelSpace S] in
@[simp] lemma coeff_one (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ)) :
    coeff mu a 1 = 0 := by simp [coeff]
omit [BorelSpace S] in
@[simp] lemma coeff_add_two (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ)) (n : ℕ) :
    coeff mu a (n + 2) =
      (cycleTrace mu a (n + 1) : ℂ) / (((2 : ℝ) * (n + 2)) : ℂ) := by
  simp [coeff]

omit [BorelSpace S] in
lemma scalar_term_add_two (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (w : ℂ) (n : ℕ) :
    coeff mu a (n + 2) * w ^ (n + 2) = unicyclicTermC mu a w n := by
  simp [unicyclicTermC, coeff_add_two]
  ring

lemma scalar_terms_tsum_eq_unicyclic (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    ∑' n : ℕ, coeff mu a n * w ^ n = ∑' n : ℕ, unicyclicTermC mu a w n := by
  let f : ℕ → ℂ := fun n => coeff mu a n * w ^ n
  have htail : Summable (fun n : ℕ => f (n + 2)) := by
    simpa only [f, scalar_term_add_two] using
      summable_unicyclicTermC mu a r hr hsubcritical w hw
  have hf : Summable f := (summable_nat_add_iff 2).mp htail
  calc
    ∑' n : ℕ, coeff mu a n * w ^ n =
        ∑ i ∈ Finset.range 2, f i + ∑' i : ℕ, f (i + 2) :=
      (hf.sum_add_tsum_nat_add 2).symm
    _ = ∑' i : ℕ, f (i + 2) := by
      have hzero : ∑ i ∈ Finset.range 2, f i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hi' : i < 2 := Finset.mem_range.mp hi
        simp [f, coeff, Nat.not_le_of_gt hi']
      rw [hzero, zero_add]
    _ = ∑' n : ℕ, unicyclicTermC mu a w n :=
      tsum_congr (scalar_term_add_two mu a w)

lemma summable_coeff_mul_pow (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1) :
    Summable (fun n : ℕ => ‖coeff mu a n‖ * r ^ n) := by
  let f : ℕ → ℝ := fun n => ‖coeff mu a n‖ * r ^ n
  have htail : Summable (fun n : ℕ => f (n + 2)) := by
    have h := summable_unicyclicTermC mu a r hr hsubcritical (r : ℂ) (by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using le_rfl)
    have heq : (fun n : ℕ => f (n + 2)) =
        fun n : ℕ => ‖unicyclicTermC mu a (r : ℂ) n‖ := by
      funext n
      dsimp [f]
      calc
        ‖coeff mu a (n + 2)‖ * r ^ (n + 2) =
            ‖coeff mu a (n + 2) * (r : ℂ) ^ (n + 2)‖ := by
              simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
        _ = ‖unicyclicTermC mu a (r : ℂ) n‖ := by
              rw [scalar_term_add_two]
    rw [heq]
    exact h.norm
  exact (summable_nat_add_iff 2).mp htail

/-- The complex direct cycle series. -/
def unicyclicSeriesC (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℂ) : ℂ :=
  ∑' n : ℕ, unicyclicTermC mu a w n

/-- The scalar power series representing the direct cycle series at the origin. -/
def unicyclicPowerSeries (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (coeff mu a)

lemma powerSeries_sum_eq_unicyclicSeriesC (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    (unicyclicPowerSeries mu a).sum w = unicyclicSeriesC mu a w := by
  change FormalMultilinearSeries.ofScalarsSum (coeff mu a) w =
    ∑' n : ℕ, unicyclicTermC mu a w n
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using scalar_terms_tsum_eq_unicyclic mu a r hr hsubcritical w hw

theorem analyticAt_unicyclicSeriesC_of_subcritical_radius
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (r : ℝ) (hr : 0 < r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    {w : ℂ} (hw : ‖w‖ < r) :
    AnalyticAt ℂ (unicyclicSeriesC mu a) w := by
  let R : ℝ≥0 := ⟨r, hr.le⟩
  let p := unicyclicPowerSeries mu a
  have hsum : Summable (fun n : ℕ => ‖p n‖ * (R : ℝ) ^ n) := by
    dsimp [p, R, unicyclicPowerSeries]
    simp only [FormalMultilinearSeries.ofScalars_norm]
    exact summable_coeff_mul_pow mu a r hr.le hsubcritical
  have hrad : (R : ℝ≥0∞) ≤ p.radius :=
    p.le_radius_of_summable_norm hsum
  have hRpos : (0 : ℝ≥0∞) < R := by
    exact_mod_cast hr
  have hpr : 0 < p.radius := lt_of_lt_of_le hRpos hrad
  have hp : HasFPowerSeriesOnBall p.sum p 0 (R : ℝ≥0∞) :=
    (p.hasFPowerSeriesOnBall hpr).mono hRpos hrad
  have hwin : w ∈ Metric.eball (0 : ℂ) (R : ℝ≥0∞) := by
    rw [mem_eball_zero_iff]
    rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe]
    rw [← NNReal.coe_lt_coe]
    change ‖w‖ < r
    exact hw
  apply (hp.analyticAt_of_mem hwin).congr
  let eps : ℝ := (r - ‖w‖) / 2
  have heps : 0 < eps := by dsimp [eps]; linarith
  apply Filter.eventually_of_mem (Metric.ball_mem_nhds w heps)
  intro z hz
  have hznorm : ‖z‖ ≤ r := by
    have hdist : dist z w < eps := Metric.mem_ball.mp hz
    apply le_of_lt
    calc
      ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ = dist z w + ‖w‖ := by rw [dist_eq_norm]
      _ < eps + ‖w‖ := by linarith
      _ ≤ r := by dsimp [eps]; linarith
  exact powerSeries_sum_eq_unicyclicSeriesC mu a r hr.le hsubcritical z hznorm

theorem differentiableAt_unicyclicSeriesC_of_subcritical_radius
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (r : ℝ) (hr : 0 < r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    {w : ℂ} (hw : ‖w‖ < r) :
    DifferentiableAt ℂ (unicyclicSeriesC mu a) w :=
  (analyticAt_unicyclicSeriesC_of_subcritical_radius mu a r hr hsubcritical hw).differentiableAt

end PerronWright.KernelCycle

