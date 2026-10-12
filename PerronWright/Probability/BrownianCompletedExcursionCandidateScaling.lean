import PerronWright.Probability.BrownianCompletedExcursionCandidate
import PerronWright.Probability.BrownianMinimumFutureScaledStrongMarkov
import PerronWright.Probability.BrownianMinimumSplitCandidate
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Exact scale and lifetime Jacobian of the completed-excursion candidate

This is a deterministic pushforward of the normalized candidate, not an
assumed identification with an actual source. The lifetime Jacobian is
proved from real Lebesgue multiplication and retains arbitrary Borel path
tests. Its physical-time density is sqrt(r)/(2*l*sqrt(l)) for l > r.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionCandidateScaling

open BrownianPathLaw BrownianPathDilationLaw BrownianMinimumFutureReturnDensity
open BrownianCompletedExcursionCandidate BrownianEntranceDurationScaling
open BrownianMinimumFuturePostUnit

def scaleTaggedPast (r : ℝ≥0) (q : ℝ≥0 × Path) : ℝ≥0 × Path :=
  (r*q.1,brownianDilation r q.2)

theorem measurable_scaleTaggedPast (r : ℝ≥0) : Measurable (scaleTaggedPast r) :=
  (measurable_const.mul measurable_fst).prodMk
    ((measurable_brownianDilation r).comp measurable_snd)

def scaledCandidateLaw (r : ℝ≥0) : Measure (ℝ≥0 × Path) :=
  candidateLaw.map (scaleTaggedPast r)

instance scaledCandidateLaw_isProbability (r : ℝ≥0) : IsProbabilityMeasure (scaledCandidateLaw r) := by
  let := candidateLaw_isProbability
  exact Measure.isProbabilityMeasure_map (measurable_scaleTaggedPast r).aemeasurable

def lifetimeDensity (r : ℝ≥0) (l : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ioi (r : ℝ)).indicator (fun l ↦ Real.sqrt (r : ℝ)/(2*l*Real.sqrt l)) l)

theorem measurable_lifetimeDensity (r : ℝ≥0) : Measurable (lifetimeDensity r) := by
  have hm : Measurable (fun l : ℝ ↦ Real.sqrt (r : ℝ)/(2*l*Real.sqrt l)) := by fun_prop
  exact (hm.indicator measurableSet_Ioi).ennreal_ofReal

theorem brownianDilation_comp (r c : ℝ≥0) (e : Path) :
    brownianDilation r (brownianDilation c e) = brownianDilation (r*c) e := by
  apply ContinuousMap.ext
  intro t
  change Real.sqrt (r : ℝ)*(Real.sqrt (c : ℝ)*e ((t/r)/c)) =
    Real.sqrt ((r*c : ℝ≥0) : ℝ)*e (t/(r*c))
  rw [NNReal.coe_mul,Real.sqrt_mul (show 0 ≤ (r : ℝ) from r.coe_nonneg),div_div]
  ring

private theorem lifetimeDensity_jacobian (r : ℝ≥0) (hr : 0 < r) (l : ℝ) :
    ENNReal.ofReal ((r : ℝ)⁻¹)*returnDensity (l/(r : ℝ)) = lifetimeDensity r l := by
  have hrR : 0 < (r : ℝ) := hr
  by_cases hl : (r : ℝ) < l
  · have hl0 : 0 < l := hrR.trans hl
    have hdiv : 1 < l/(r : ℝ) := (lt_div_iff₀ hrR).mpr (by simpa using hl)
    unfold returnDensity lifetimeDensity
    rw [indicator_of_mem (show l/(r : ℝ) ∈ Ioi (1 : ℝ) from hdiv),
      indicator_of_mem (show l ∈ Ioi (r : ℝ) from hl)]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hrR.le)]
    congr 1
    rw [Real.sqrt_div hl0.le]
    have hs : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrR)
    have hsl : Real.sqrt l ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hl0)
    field_simp
  · have hdiv : l/(r : ℝ) ∉ Ioi (1 : ℝ) := by
      simpa only [mem_Ioi,not_lt] using (div_le_one hrR).mpr (le_of_not_gt hl)
    unfold returnDensity lifetimeDensity
    rw [indicator_of_notMem hdiv,indicator_of_notMem (show l ∉ Ioi (r : ℝ) from hl)]
    simp only [ENNReal.ofReal_zero,mul_zero]

theorem lintegral_lifetime_scaling (r : ℝ≥0) (hr : 0 < r)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ z : ℝ, returnDensity z*H ((r : ℝ)*z)) =
      ∫⁻ l : ℝ, lifetimeDensity r l*H l := by
  let J : ℝ → ℝ≥0∞ := fun l ↦ returnDensity (l/(r : ℝ))*H l
  have hJ : Measurable J :=
    (measurable_returnDensity.comp (measurable_id.div_const _)).mul hH
  calc
    _ = ∫⁻ z : ℝ, J ((r : ℝ)*z) := by
      apply lintegral_congr
      intro z
      simp only [J,mul_div_cancel_left₀ z (show (r : ℝ) ≠ 0 from ne_of_gt hr)]
    _ = ∫⁻ l : ℝ, J l ∂volume.map (fun z : ℝ ↦ (r : ℝ)*z) :=
      (lintegral_map hJ (measurable_const.mul measurable_id)).symm
    _ = ENNReal.ofReal ((r : ℝ)⁻¹)*(∫⁻ l : ℝ, J l) := by
      rw [Real.map_volume_mul_left (show (r : ℝ) ≠ 0 from ne_of_gt hr),
        abs_of_nonneg (inv_nonneg.mpr r.coe_nonneg),lintegral_smul_measure]
      rfl
    _ = _ := by
      rw [← lintegral_const_mul _ hJ]
      apply lintegral_congr
      intro l
      change ENNReal.ofReal ((r : ℝ)⁻¹)*(returnDensity (l/(r : ℝ))*H l) = _
      rw [← mul_assoc,lifetimeDensity_jacobian r hr l]

theorem lintegral_scaledCandidateLaw (r : ℝ≥0) (hr : 0 < r)
    (Ψ : ℝ≥0 × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ q, Ψ q ∂scaledCandidateLaw r) =
      ∫⁻ l : ℝ, lifetimeDensity r l*(∫⁻ e : Path,
        Ψ (Real.toNNReal l,brownianDilation (Real.toNNReal l) e)
          ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability 1 zero_lt_one
  let H : ℝ → ℝ≥0∞ := fun l ↦ ∫⁻ e : Path,
    Ψ (Real.toNNReal l,brownianDilation (Real.toNNReal l) e)
      ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one
  have hm : Measurable (fun q : ℝ × Path ↦
      Ψ (Real.toNNReal q.1,brownianDilation (Real.toNNReal q.1) q.2)) :=
    hΨ.comp (measurable_fst.real_toNNReal.prodMk (measurable_joint_brownianDilation.comp
      (measurable_fst.real_toNNReal.prodMk measurable_snd)))
  have hH : Measurable H := hm.lintegral_prod_right'
  rw [scaledCandidateLaw,lintegral_map hΨ (measurable_scaleTaggedPast r)]
  change (∫⁻ q, (Ψ ∘ scaleTaggedPast r) q ∂candidateLaw) = _
  rw [lintegral_candidateLaw _ (hΨ.comp (measurable_scaleTaggedPast r))]
  calc
    _ = ∫⁻ z : ℝ, returnDensity z*H ((r : ℝ)*z) := by
      apply lintegral_congr
      intro z
      by_cases hz : 1 < z
      · have he : Real.toNNReal ((r : ℝ)*z) = r*Real.toNNReal z := by
          rw [Real.toNNReal_mul r.coe_nonneg,Real.toNNReal_coe]
        change returnDensity z*(∫⁻ e : Path,
          Ψ (r*Real.toNNReal z,brownianDilation r (brownianDilation (Real.toNNReal z) e))
            ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) =
          returnDensity z*(∫⁻ e : Path,
            Ψ (Real.toNNReal ((r : ℝ)*z),brownianDilation (Real.toNNReal ((r : ℝ)*z)) e)
              ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one)
        rw [he]
        congr 1
        apply lintegral_congr
        intro e
        rw [brownianDilation_comp r (Real.toNNReal z)]
      · simp [returnDensity,indicator_of_notMem (show z ∉ Ioi (1 : ℝ) from hz)]
    _ = _ := lintegral_lifetime_scaling r hr hH

theorem entrance_lifetime_weight_eq (r : ℝ≥0) (hr : 0 < r) (l : ℝ) :
    (ENNReal.ofReal BrownianMinimumSplitCandidate.entranceCoefficient*
      ENNReal.ofReal (1/Real.sqrt (r : ℝ)))*lifetimeDensity r l =
        (Ioi (r : ℝ)).indicator
          (fun l ↦ ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*l*Real.sqrt l))) l := by
  by_cases hl : (r : ℝ) < l
  · have hl0 : 0 < l := lt_trans hr hl
    have hsr : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr)
    have hsl : Real.sqrt l ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hl0)
    have hsπ : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hcoef : BrownianMinimumSplitCandidate.entranceCoefficient/2 =
        1/Real.sqrt (2*Real.pi) := by
      have hp : Real.sqrt (2/Real.pi)*Real.sqrt (2*Real.pi) = 2 := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ 2/Real.pi)]
        have he : (2/Real.pi)*(2*Real.pi) = 4 := by field_simp; ring
        rw [he]
        norm_num
      apply (div_eq_div_iff (by norm_num : (2 : ℝ) ≠ 0) hsπ).mpr
      simpa only [BrownianMinimumSplitCandidate.entranceCoefficient,one_mul] using hp
    unfold lifetimeDensity
    rw [indicator_of_mem (show l ∈ Ioi (r : ℝ) from hl),
      indicator_of_mem (show l ∈ Ioi (r : ℝ) from hl),
      ← ENNReal.ofReal_mul (by
        dsimp [BrownianMinimumSplitCandidate.entranceCoefficient]
        positivity : 0 ≤ BrownianMinimumSplitCandidate.entranceCoefficient),
      ← ENNReal.ofReal_mul (by
        dsimp [BrownianMinimumSplitCandidate.entranceCoefficient]
        positivity : 0 ≤ BrownianMinimumSplitCandidate.entranceCoefficient*(1/Real.sqrt (r : ℝ)))]
    congr 1
    calc
      _ = (BrownianMinimumSplitCandidate.entranceCoefficient/2)/(l*Real.sqrt l) := by
        field_simp
      _ = _ := by rw [hcoef]; ring
  · unfold lifetimeDensity
    rw [indicator_of_notMem (show l ∉ Ioi (r : ℝ) from hl),
      indicator_of_notMem (show l ∉ Ioi (r : ℝ) from hl)]
    simp only [ENNReal.ofReal_zero,mul_zero]

end PerronWright.BrownianCompletedExcursionCandidateScaling
