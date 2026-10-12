import PerronWright.Probability.ProfileSquareMoment
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integral transfer for bounded concentrated remainders

The underlying probability spaces and measures may vary with the index.
All integral conclusions are derived from literal event probabilities
and literal exponential moments, not a uniform-integrability interface.
-/

open MeasureTheory Filter Topology
open scoped Topology Real

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BoundedConcentrationTransfer

open ProfileSquareMoment

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_abs_le_threshold_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) {B ε : ℝ} (_hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbound : ∀ ω, |X ω| ≤ B) :
    (∫ ω, |X ω| ∂μ) ≤ ε + B * μ.real {ω | ε ≤ |X ω|} := by
  have hmeas : Measurable (fun ω ↦ |X ω|) := by simpa only [Real.norm_eq_abs] using hX.norm
  have hset : MeasurableSet {ω | ε ≤ |X ω|} := measurableSet_le measurable_const hmeas
  have hint : Integrable (fun ω ↦ |X ω|) μ :=
    (integrable_of_measurable_abs_le μ hX hbound).norm
  have hind : Integrable ({ω | ε ≤ |X ω|}.indicator (fun _ : Ω ↦ B)) μ :=
    (integrable_const B).indicator hset
  have hpoint (ω : Ω) : |X ω| ≤ ε + {ω | ε ≤ |X ω|}.indicator (fun _ : Ω ↦ B) ω := by
    by_cases hω : ε ≤ |X ω|
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ε ≤ |X ω|} from hω)]
      exact (hbound ω).trans (by linarith)
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ε ≤ |X ω|} from hω),add_zero]
      exact (lt_of_not_ge hω).le
  have hi := integral_mono hint ((integrable_const ε).add hind) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const ε) hind,integral_const,
    integral_indicator_const B hset] at hi
  simpa only [probReal_univ,smul_eq_mul,one_mul,mul_one,mul_comm] using hi

/-- Bounded convergence in probability gives a proved L1 conclusion,
even on changing sampling spaces. -/
theorem integral_abs_tendsto_zero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, Measurable (X n))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ n ω, |X n ω| ≤ B)
    (hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ (μ n).real {ω | ε ≤ |X n ω|}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, |X n ω| ∂μ n) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n ↦ ha.trans_le (integral_nonneg (fun _ ↦ abs_nonneg _)))
  · intro ε hε
    have ht := (hprob (ε / 2) (by positivity)).const_mul B
    have hu := (tendsto_const_nhds (x := ε / 2)).add ht
    simp only [mul_zero,add_zero] at hu
    filter_upwards [hu.eventually (Iio_mem_nhds (by linarith : ε / 2 < ε))] with n hn
    exact (integral_abs_le_threshold_tail (μ n) (X n) (hX n) hB
      (by positivity : 0 ≤ ε / 2) (hbound n)).trans_lt hn

theorem abs_exp_sub_one_le_exp_abs_sub_one (x : ℝ) :
    |Real.exp x - 1| ≤ Real.exp |x| - 1 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx,abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hx))]
  · have hneg := (lt_of_not_ge hx).le
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hneg)),abs_of_nonpos hneg]
    have hp := Real.add_one_le_exp x
    have hn := Real.add_one_le_exp (-x)
    linarith

theorem abs_exp_sub_one_le_bound {x B : ℝ} (hx : |x| ≤ B) :
    |Real.exp x - 1| ≤ Real.exp B * |x| := by
  calc
    _ ≤ Real.exp |x| - 1 := abs_exp_sub_one_le_exp_abs_sub_one x
    _ ≤ |x| * Real.exp |x| := exp_sub_one_le_mul_exp _
    _ ≤ |x| * Real.exp B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (abs_nonneg _)
    _ = _ := mul_comm _ _

theorem abs_exp_add_sub_one_le {a b B : ℝ} (hb : |b| ≤ B) :
    |Real.exp (a+b)-1| ≤
      Real.exp B * (Real.exp |a| - 1) + Real.exp B * |b| := by
  have he : Real.exp (a+b)-1 = Real.exp b * (Real.exp a - 1) + (Real.exp b - 1) := by
    rw [Real.exp_add]
    ring
  rw [he]
  calc
    _ ≤ |Real.exp b * (Real.exp a - 1)| + |Real.exp b - 1| := abs_add_le _ _
    _ = Real.exp b * |Real.exp a - 1| + |Real.exp b - 1| := by
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp B * (Real.exp |a| - 1) + Real.exp B * |b| := by
      apply add_le_add
      · exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self b).trans hb))
          (abs_exp_sub_one_le_exp_abs_sub_one a) (abs_nonneg _) (Real.exp_pos _).le
      · exact abs_exp_sub_one_le_bound hb

/-- A direct L1 exponential bound combining the quadratic exponential
moment and a bounded scalar remainder. -/
theorem integral_abs_exp_add_sub_one_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Q Z : Ω → ℝ) (hQ : Measurable Q) (hZ : Measurable Z) {B : ℝ}
    (hbound : ∀ ω, |Z ω| ≤ B)
    (hQE : Integrable (fun ω ↦ Real.exp |Q ω|) μ) :
    (∫ ω, |Real.exp (Q ω + Z ω)-1| ∂μ) ≤
      Real.exp B * ((∫ ω, Real.exp |Q ω| ∂μ)-1) +
        Real.exp B * (∫ ω, |Z ω| ∂μ) := by
  have hZi : Integrable (fun ω ↦ |Z ω|) μ :=
    (integrable_of_measurable_abs_le μ hZ hbound).norm
  have hU : Integrable (fun ω ↦ Real.exp B * (Real.exp |Q ω| - 1) +
      Real.exp B * |Z ω|) μ :=
    ((hQE.sub (integrable_const 1)).const_mul _).add (hZi.const_mul _)
  have hmeas : Measurable (fun ω ↦ |Real.exp (Q ω + Z ω)-1|) := by
    simpa only [Real.norm_eq_abs,Pi.add_apply,Pi.sub_apply] using
      ((hQ.add hZ).exp.sub measurable_const).norm
  have hi : Integrable (fun ω ↦ |Real.exp (Q ω + Z ω)-1|) μ :=
    hU.mono_nonneg hmeas.aestronglyMeasurable (Eventually.of_forall (fun _ ↦ abs_nonneg _))
      (Eventually.of_forall (fun ω ↦ abs_exp_add_sub_one_le (hbound ω)))
  have hu := integral_mono hi hU (fun ω ↦ abs_exp_add_sub_one_le (hbound ω))
  have hleft : Integrable (fun ω ↦ Real.exp B * (Real.exp |Q ω| - 1)) μ := by
    simpa only [Pi.sub_apply] using (hQE.sub (integrable_const 1)).const_mul (Real.exp B)
  rw [integral_add hleft (hZi.const_mul (Real.exp B)),
    integral_const_mul,integral_const_mul,integral_sub hQE (integrable_const 1),
    integral_const] at hu
  simpa only [probReal_univ,smul_eq_mul,one_mul] using hu

/-- Actual exponential-moment control plus bounded probability
concentration implies the exponential residual converges to one in L1. -/
theorem integral_abs_exp_add_sub_one_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Q Z : ∀ n, Ω n → ℝ) (hQ : ∀ n, Measurable (Q n)) (hZ : ∀ n, Measurable (Z n))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ n ω, |Z n ω| ≤ B)
    (hQE : ∀ n, Integrable (fun ω ↦ Real.exp |Q n ω|) (μ n))
    (hQt : Tendsto (fun n ↦ ∫ ω, Real.exp |Q n ω| ∂μ n) atTop (𝓝 1))
    (hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ (μ n).real {ω | ε ≤ |Z n ω|}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, |Real.exp (Q n ω + Z n ω)-1| ∂μ n) atTop (𝓝 0) := by
  have hZt := integral_abs_tendsto_zero μ Z hZ B hB hbound hprob
  have hu := ((hQt.sub_const 1).const_mul (Real.exp B)).add (hZt.const_mul (Real.exp B))
  simp only [sub_self,mul_zero,zero_add] at hu
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _)))
    (Eventually.of_forall (fun n ↦ integral_abs_exp_add_sub_one_le (μ n) (Q n) (Z n)
      (hQ n) (hZ n) (hbound n) (hQE n))) hu

theorem exp_add_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Q Z : Ω → ℝ) (hQ : Measurable Q) (hZ : Measurable Z) {B : ℝ}
    (hbound : ∀ ω, |Z ω| ≤ B)
    (hQE : Integrable (fun ω ↦ Real.exp |Q ω|) μ) :
    Integrable (fun ω ↦ Real.exp (Q ω + Z ω)) μ := by
  apply (hQE.const_mul (Real.exp B)).mono' ((hQ.add hZ).exp).aestronglyMeasurable
  exact Eventually.of_forall (fun ω ↦ by
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [le_abs_self (Q ω),le_abs_self (Z ω),hbound ω]))

/-- The literal exponential residual expectation tends to one, as a
consequence of the proved L1 estimate rather than an assumed limit. -/
theorem integral_exp_add_tendsto_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Q Z : ∀ n, Ω n → ℝ) (hQ : ∀ n, Measurable (Q n)) (hZ : ∀ n, Measurable (Z n))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ n ω, |Z n ω| ≤ B)
    (hQE : ∀ n, Integrable (fun ω ↦ Real.exp |Q n ω|) (μ n))
    (hQt : Tendsto (fun n ↦ ∫ ω, Real.exp |Q n ω| ∂μ n) atTop (𝓝 1))
    (hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ (μ n).real {ω | ε ≤ |Z n ω|}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, Real.exp (Q n ω + Z n ω) ∂μ n) atTop (𝓝 1) := by
  have hL := integral_abs_exp_add_sub_one_tendsto_zero μ Q Z hQ hZ B hB hbound hQE hQt hprob
  have habs : Tendsto (fun n ↦ |(∫ ω, Real.exp (Q n ω + Z n ω) ∂μ n)-1|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hL
    exact Eventually.of_forall (fun n ↦ by
      have hi := exp_add_integrable (μ n) (Q n) (Z n) (hQ n) (hZ n) (hbound n) (hQE n)
      have h := MeasureTheory.abs_integral_le_integral_abs
        (μ := μ n) (f := fun ω ↦ Real.exp (Q n ω + Z n ω)-1)
      rw [integral_sub hi (integrable_const 1),integral_const] at h
      simpa only [probReal_univ,smul_eq_mul,one_mul] using h)
  rw [← tendsto_sub_nhds_zero_iff]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

end PerronWright.BoundedConcentrationTransfer
