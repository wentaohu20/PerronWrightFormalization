import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalOnePoint
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Full Borel one-point law of the actual positive pinned bridge

The preceding actual tail identity determines the whole one-point measure,
not merely a selection of its moments. Its density is a genuine entrance
times exit killed kernel divided by the true positive-bridge normalization.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeFiniteDimensionalLaw

open BrownianPathLaw BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel
open BrownianPositiveBridgeConditioning BrownianPositiveBridgeFiniteDimensionalOnePoint

def normalization (a : ℝ) (T : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (1-Real.exp (-2*a^2/(T : ℝ)))

def onePointDensity (a : ℝ) (s t : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  (normalization a (s+t))⁻¹*(density a s x*density x t a)/gaussianPDF 0 (s+t) 0

theorem measurable_onePointDensity (a : ℝ) (s t : ℝ≥0) : Measurable (onePointDensity a s t) := by
  have hp : Measurable (fun x : ℝ ↦ (x,a)) := measurable_id.prodMk measurable_const
  have hc := (BrownianPositiveKilledKernel.measurable_joint_density t).comp hp
  have hm : Measurable (fun x : ℝ ↦ density x t a) := by simpa only [Function.comp_def] using hc
  unfold onePointDensity
  simp only [div_eq_mul_inv]
  exact (measurable_const.mul ((measurable_density a s).mul hm)).mul_const _

theorem onePointDensity_tail_integral (a : ℝ) (s t : ℝ≥0) (hs : 0 < s) (c : ℝ) :
    (∫⁻ x in Ioi c, onePointDensity a s t x) =
      (normalization a (s+t))⁻¹*(∫⁻ x in Ioi c, density x t a ∂law a s)/gaussianPDF 0 (s+t) 0 := by
  have hp : Measurable (fun x : ℝ ↦ (x,a)) := measurable_id.prodMk measurable_const
  have hc := (BrownianPositiveKilledKernel.measurable_joint_density t).comp hp
  have hm : Measurable (fun x : ℝ ↦ density x t a) := by simpa only [Function.comp_def] using hc
  rw [law_eq_withDensity_all a s hs,setLIntegral_withDensity_eq_setLIntegral_mul volume
    (measurable_density a s) hm measurableSet_Ioi]
  simp only [onePointDensity,div_eq_mul_inv,Pi.mul_apply]
  have hprod : Measurable (fun x : ℝ ↦ density a s x*density x t a) := (measurable_density a s).mul hm
  have hconst : Measurable (fun x : ℝ ↦ (normalization a (s+t))⁻¹*(density a s x*density x t a)) :=
    measurable_const.mul hprod
  calc
    _ = (∫⁻ x in Ioi c, (normalization a (s+t))⁻¹*(density a s x*density x t a)) *
        (gaussianPDF 0 (s+t) 0)⁻¹ := lintegral_mul_const _ hconst
    _ = _ := by rw [lintegral_const_mul _ hprod]

theorem onePointLaw_eq_withDensity (a : ℝ) (ha : 0 < a) (s t : ℝ≥0)
    (hs : 0 < s) (ht : 0 < t) :
    (positiveBridgeLaw a (s+t)).map (fun g : Path ↦ g s) =
      volume.withDensity (onePointDensity a s t) := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  let : IsProbabilityMeasure (positiveBridgeLaw a (s+t)) := positiveBridgeLaw_isProbability a ha (s+t) hT
  let μ := (positiveBridgeLaw a (s+t)).map (fun g : Path ↦ g s)
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (continuous_eval s).measurable.aemeasurable
  apply Measure.ext_of_generateFrom_of_iUnion (range (Ioi : ℝ → Set ℝ))
    (fun n : ℕ ↦ Ioi (-(n : ℝ)))
    (show (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom (range (Ioi : ℝ → Set ℝ)) from by
      exact borel_eq_generateFrom_Ioi ℝ) isPiSystem_Ioi
  · ext x
    simp only [mem_iUnion,mem_Ioi,mem_univ,iff_true]
    obtain ⟨n,hn⟩ := exists_nat_gt (-x)
    exact ⟨n,by linarith⟩
  · intro n
    exact ⟨-(n : ℝ),rfl⟩
  · intro n
    exact measure_ne_top μ _
  · rintro B ⟨c,rfl⟩
    rw [Measure.map_apply (continuous_eval s).measurable measurableSet_Ioi]
    change positiveBridgeLaw a (s+t) {g | c < g s} = _
    rw [positiveBridgeLaw_onePoint_tail a ha s t ht c,withDensity_apply _ measurableSet_Ioi,
      onePointDensity_tail_integral a s t hs c]
    rfl

theorem onePoint_lintegral (a : ℝ) (ha : 0 < a) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ g, Ψ (g s) ∂positiveBridgeLaw a (s+t)) = ∫⁻ x, onePointDensity a s t x*Ψ x := by
  rw [← lintegral_map hΨ (continuous_eval s).measurable,onePointLaw_eq_withDensity a ha s t hs ht,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_onePointDensity a s t) hΨ]
  rfl

theorem onePoint_density_integral_eq_one (a : ℝ) (ha : 0 < a) (s t : ℝ≥0)
    (hs : 0 < s) (ht : 0 < t) : (∫⁻ x, onePointDensity a s t x) = 1 := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  let : IsProbabilityMeasure (positiveBridgeLaw a (s+t)) := positiveBridgeLaw_isProbability a ha (s+t) hT
  simpa only [mul_one,lintegral_one,measure_univ] using
    (onePoint_lintegral a ha s t hs ht (fun _ ↦ 1) measurable_const).symm

end PerronWright.BrownianPositiveBridgeFiniteDimensionalLaw
