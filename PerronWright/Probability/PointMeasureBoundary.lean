import PerronWright.Probability.FinitePointMeasurePolish
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Open-cell Portmanteau bounds for actual point-measure laws

Open-cell point mass is lower semicontinuous in the genuine weak point
topology. Layer cake and open-set Portmanteau transfer actual source
expectation bounds to weak law limits, in the lower-semicontinuous
direction. Vanishing open neighborhoods then give almost sure absence
of points on the enclosed boundary.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.PointMeasureBoundary

open FinitePointMeasureCompact FinitePointMeasureMeasurable FinitePointMeasurePolish

variable {E : Type*} [MeasurableSpace E] [MetricSpace E] [CompactSpace E]
  [BorelSpace E] [Nonempty E]

omit [MetricSpace E] [CompactSpace E] [BorelSpace E] in
theorem eval_eq_mass_mul_normalize (η : PointMeasure E) (A : Set E) :
    ((η : FiniteMeasure E) : Measure E) A =
      (mass η : ℝ≥0∞) * ((η : FiniteMeasure E).normalize : Measure E) A := by
  have hh := congrArg (fun μ : FiniteMeasure E ↦ (μ : Measure E) A)
    (FiniteMeasure.self_eq_mass_smul_normalize (η : FiniteMeasure E))
  simpa only [FiniteMeasure.toMeasure_smul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure, mass] using hh

omit [CompactSpace E] in
theorem lowerSemicontinuous_eval_open {A : Set E} (hA : IsOpen A) :
    LowerSemicontinuous (fun η : PointMeasure E ↦ ((η : FiniteMeasure E) : Measure E) A) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro η
  have hs : ∀ᶠ ζ in 𝓝 η, size ζ = size η := by
    exact (continuous_size.tendsto η).eventually
      ((isOpen_discrete ({size η} : Set ℕ)).mem_nhds (by simp))
  have hm : ∀ᶠ ζ in 𝓝 η, mass ζ = mass η := hs.mono (fun ζ hζ ↦ by
    rw [mass_eq_size, mass_eq_size, hζ])
  have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (continuous_normalize.tendsto η) hA
  rw [eval_eq_mass_mul_normalize η A]
  calc
    (mass η : ℝ≥0∞) * ((η : FiniteMeasure E).normalize : Measure E) A ≤
        (mass η : ℝ≥0∞) * liminf (fun ζ : PointMeasure E ↦
          ((ζ : FiniteMeasure E).normalize : Measure E) A) (𝓝 η) := mul_le_mul_right hp _
    _ = liminf (fun ζ : PointMeasure E ↦ (mass η : ℝ≥0∞) *
          ((ζ : FiniteMeasure E).normalize : Measure E) A) (𝓝 η) :=
      (ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top).symm
    _ = liminf (fun ζ : PointMeasure E ↦ ((ζ : FiniteMeasure E) : Measure E) A) (𝓝 η) := by
      apply liminf_congr
      filter_upwards [hm] with ζ hζ
      rw [eval_eq_mass_mul_normalize ζ A, hζ]

omit [CompactSpace E] in
theorem lowerSemicontinuous_eval_real_open {A : Set E} (hA : IsOpen A) :
    LowerSemicontinuous (fun η : PointMeasure E ↦ ((η : FiniteMeasure E) : Measure E).real A) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro t
  by_cases ht : t < 0
  · have he : (fun η : PointMeasure E ↦ ((η : FiniteMeasure E) : Measure E).real A) ⁻¹'
        Set.Ioi t = Set.univ := by
      ext η
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact ht.trans_le measureReal_nonneg
    rw [he]
    exact isOpen_univ
  · have ht' : 0 ≤ t := le_of_not_gt ht
    have he : (fun η : PointMeasure E ↦ ((η : FiniteMeasure E) : Measure E).real A) ⁻¹'
        Set.Ioi t = (fun η : PointMeasure E ↦ ((η : FiniteMeasure E) : Measure E) A) ⁻¹'
          Set.Ioi (ENNReal.ofReal t) := by
      ext η
      exact (ENNReal.ofReal_lt_iff_lt_toReal ht' (by finiteness)).symm
    rw [he]
    exact (lowerSemicontinuous_eval_open hA).isOpen_preimage _

/-- Layer-cake proof of the lower-semicontinuous law Portmanteau
inequality. Neither boundedness nor a uniform-integrability premise is
required for this nonnegative lower bound. -/
theorem lintegral_lsc_le_liminf {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [BorelSpace Ω] [HasOuterApproxClosed Ω]
    (νs : ℕ → ProbabilityMeasure Ω) (ν : ProbabilityMeasure Ω)
    (hν : Tendsto νs atTop (𝓝 ν)) (f : Ω → ℝ)
    (hf : LowerSemicontinuous f) (hnn : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure Ω)) ≤
      liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(νs n : Measure Ω)) atTop := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall hnn) hf.measurable.aemeasurable]
  apply (lintegral_mono (fun t ↦
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν (hf.isOpen_preimage t))).trans
  exact lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
    measure_mono (fun x hx ↦ lt_of_le_of_lt hst hx)))

theorem lintegral_eval_open_le_liminf
    (νs : ℕ → ProbabilityMeasure (PointMeasure E)) (ν : ProbabilityMeasure (PointMeasure E))
    (hν : Tendsto νs atTop (𝓝 ν)) {A : Set E} (hA : IsOpen A) :
    (∫⁻ η, ((η : FiniteMeasure E) : Measure E) A ∂(ν : Measure (PointMeasure E))) ≤
      liminf (fun n ↦ ∫⁻ η, ((η : FiniteMeasure E) : Measure E) A
        ∂(νs n : Measure (PointMeasure E))) atTop := by
  have hh := lintegral_lsc_le_liminf νs ν hν
    (fun η ↦ ((η : FiniteMeasure E) : Measure E).real A)
    (lowerSemicontinuous_eval_real_open hA) (fun _ ↦ measureReal_nonneg)
  have he (η : PointMeasure E) :
      ENNReal.ofReal (((η : FiniteMeasure E) : Measure E).real A) =
        ((η : FiniteMeasure E) : Measure E) A :=
    ENNReal.ofReal_toReal (by finiteness)
  simpa only [he] using hh

/-- Genuine eventual real first-moment bounds pass to the open-cell
expected point mass of an actual weak probability-law limit. -/
theorem lintegral_eval_open_le_of_eventual_bound
    (νs : ℕ → ProbabilityMeasure (PointMeasure E)) (ν : ProbabilityMeasure (PointMeasure E))
    (hν : Tendsto νs atTop (𝓝 ν)) {A : Set E} (hA : IsOpen A)
    (hint : ∀ n, Integrable (fun η : PointMeasure E ↦ ((η : FiniteMeasure E) : Measure E).real A)
      (νs n : Measure (PointMeasure E)))
    (g : ℕ → ℝ) (L : ℝ) (hg : Tendsto g atTop (𝓝 L))
    (hbound : ∀ᶠ n in atTop,
      (∫ η, ((η : FiniteMeasure E) : Measure E).real A
        ∂(νs n : Measure (PointMeasure E))) ≤ g n) :
    (∫⁻ η, ((η : FiniteMeasure E) : Measure E) A ∂(ν : Measure (PointMeasure E))) ≤
      ENNReal.ofReal L := by
  apply (lintegral_eval_open_le_liminf νs ν hν hA).trans
  have hb : ∀ᶠ n in atTop,
      (∫⁻ η, ((η : FiniteMeasure E) : Measure E) A
        ∂(νs n : Measure (PointMeasure E))) ≤ ENNReal.ofReal (g n) := by
    filter_upwards [hbound] with n hn
    have he := ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall (fun _ ↦ measureReal_nonneg))
    have heval (η : PointMeasure E) :
        ENNReal.ofReal (((η : FiniteMeasure E) : Measure E).real A) =
          ((η : FiniteMeasure E) : Measure E) A :=
      ENNReal.ofReal_toReal (by finiteness)
    simp only [heval] at he
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hn
  exact (liminf_le_liminf hb).trans_eq ((ENNReal.continuous_ofReal.tendsto L).comp hg).liminf_eq

omit [CompactSpace E] [Nonempty E] in
/-- Vanishing actual expected open neighborhoods imply that the actual
limiting point law almost surely has no point on the enclosed Borel set. -/
theorem ae_eval_eq_zero_of_open_bounds (ν : ProbabilityMeasure (PointMeasure E))
    (A : Set E) (hA : MeasurableSet A) (U : ℕ → Set E) (hAU : ∀ m, A ⊆ U m)
    (b : ℕ → ℝ≥0∞) (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ m, (∫⁻ η, ((η : FiniteMeasure E) : Measure E) (U m)
      ∂(ν : Measure (PointMeasure E))) ≤ b m) :
    ∀ᵐ η : PointMeasure E ∂(ν : Measure (PointMeasure E)),
      ((η : FiniteMeasure E) : Measure E) A = 0 := by
  have hh : ∀ m, (∫⁻ η, ((η : FiniteMeasure E) : Measure E) A
      ∂(ν : Measure (PointMeasure E))) ≤ b m := fun m ↦
    (lintegral_mono (fun η ↦ measure_mono (hAU m))).trans (hbound m)
  have hz : (∫⁻ η, ((η : FiniteMeasure E) : Measure E) A
      ∂(ν : Measure (PointMeasure E))) = 0 := le_antisymm (ge_of_tendsto' hb hh) bot_le
  exact (lintegral_eq_zero_iff (measurable_eval hA)).mp hz

end PerronWright.PointMeasureBoundary
