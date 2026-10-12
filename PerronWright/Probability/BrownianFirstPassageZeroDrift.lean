import PerronWright.Probability.BrownianKilledSurvivalMoment

/-! # Actual zero-drift Brownian first passage is finite

The proved killed-law survival estimate gives a literal first-passage
tail bound. The event of infinite first passage is contained in every
finite-horizon survival event. At square horizons those actual masses
tend to zero. This discharges finiteness under the constructed Brownian
path law without a growth, recurrence, or strong-Markov premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageZeroDrift

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledSurvivalMoment

theorem survival_mass_eq_killed (a : ℝ) (T : ℝ≥0) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage (-a) f} =
      BrownianPositiveKilledEndpoint.law a T univ := by
  simpa only [mem_univ,and_true] using
    (BrownianPositiveKilledEndpoint.law_apply a T MeasurableSet.univ).symm

theorem survival_tail_bound (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage (-a) f} ≤
      ENNReal.ofReal (a*survivalCoefficient/Real.sqrt (T : ℝ)) := by
  have hb := (ENNReal.div_le_iff' (ENNReal.ofReal_ne_zero_iff.mpr ha)
    ENNReal.ofReal_ne_top).mp (normalized_survival_mass_bound a ha T hT)
  rw [← survival_mass_eq_killed a T] at hb
  simpa only [← ENNReal.ofReal_mul ha.le,mul_div_assoc] using hb

theorem square_horizon_tail_bound (a : ℝ) (ha : 0 < a) (n : ℕ) :
    pathLaw {f : Path | ((((n : ℝ≥0)+1)^2 : ℝ≥0) : ℝ≥0∞) < firstPassage (-a) f} ≤
      ENNReal.ofReal (a*survivalCoefficient/((n : ℝ)+1)) := by
  have he : Real.sqrt ((((n : ℝ≥0)+1)^2 : ℝ≥0) : ℝ) = (n : ℝ)+1 := by
    simp only [NNReal.coe_pow,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,
      Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)+1)]
  exact (survival_tail_bound a ha (((n : ℝ≥0)+1)^2) (by positivity)).trans_eq
    (congrArg (fun r : ℝ ↦ ENNReal.ofReal (a*survivalCoefficient/r)) he)

theorem survival_square_bound_tendsto_zero (a : ℝ) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal (a*survivalCoefficient/((n : ℝ)+1))) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ ↦ a*survivalCoefficient/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (a*survivalCoefficient)
  simpa only [Function.comp_def,ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr

theorem measure_firstPassage_neg_eq_top_zero (a : ℝ) (ha : 0 < a) :
    pathLaw {f : Path | firstPassage (-a) f = ⊤} = 0 := by
  apply le_antisymm _ zero_le
  apply ge_of_tendsto (survival_square_bound_tendsto_zero a)
  apply Eventually.of_forall
  intro n
  calc
    _ ≤ pathLaw {f : Path | ((((n : ℝ≥0)+1)^2 : ℝ≥0) : ℝ≥0∞) < firstPassage (-a) f} := by
      apply measure_mono
      intro f hf
      change firstPassage (-a) f = ⊤ at hf
      change ((((n : ℝ≥0)+1)^2 : ℝ≥0) : ℝ≥0∞) < firstPassage (-a) f
      rw [hf]
      exact ENNReal.coe_lt_top
    _ ≤ _ := square_horizon_tail_bound a ha n

theorem measure_firstPassage_eq_top_zero (level : ℝ) (hlevel : level < 0) :
    pathLaw {f : Path | firstPassage level f = ⊤} = 0 := by
  simpa only [neg_neg] using measure_firstPassage_neg_eq_top_zero (-level) (by linarith)

/-- Literal first passage under the actual zero-drift Brownian path law,
with no finiteness or recurrence hypothesis. -/
theorem ae_firstPassage_ne_top (level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f : Path ∂pathLaw, firstPassage level f ≠ ⊤ := by
  apply ae_iff.mpr
  simpa only [not_not] using measure_firstPassage_eq_top_zero level hlevel

theorem ae_firstPassage_lt_top (level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f : Path ∂pathLaw, firstPassage level f < ⊤ :=
  (ae_firstPassage_ne_top level hlevel).mono (fun _ hf ↦ lt_top_iff_ne_top.mpr hf)

theorem ae_firstPassage_pos (level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f : Path ∂pathLaw, 0 < firstPassage level f := by
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  by_contra hn
  obtain ⟨t,ht,hhit⟩ := (firstPassage_le_iff level f 0).mp (le_of_not_gt hn)
  have ht0 : t = 0 := le_antisymm ht zero_le
  subst t
  rw [hf] at hhit
  exact (not_le_of_gt hlevel) hhit

theorem ae_firstPassage_exact_level (level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f : Path ∂pathLaw, f (firstPassage level f).toNNReal = level := by
  filter_upwards [ae_firstPassage_ne_top level hlevel,
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hfin hf
  exact firstPassage_exact_level level f (by simpa only [hf] using hlevel) hfin

end PerronWright.BrownianFirstPassageZeroDrift
