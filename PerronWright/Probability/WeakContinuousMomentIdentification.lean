import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Identification of actual unbounded moments under weak convergence

Bounded continuous minimum tests and monotone convergence control the
target moment. A proved quadratic truncation remainder then identifies
an actual source moment limit. Neither target finiteness nor uniform
integrability is an input.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.WeakContinuousMomentIdentification

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def truncateTest (h : X → ℝ) (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x)
    (B : ℝ) (hB : 0 ≤ B) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ min (h x) B)
    (hc.min continuous_const) B (fun x ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (h0 x) hB)]
      exact min_le_right _ _)

omit [MeasurableSpace X] [BorelSpace X] in
theorem truncateTest_nonneg (h : X → ℝ) (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x)
    (B : ℝ) (hB : 0 ≤ B) (x : X) : 0 ≤ truncateTest h hc h0 B hB x :=
  le_min (h0 x) hB

theorem truncate_lintegral_tendsto {ι : Type*} {L : Filter ι}
    (μ : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X) (hweak : Tendsto μ L (𝓝 ν))
    (h : X → ℝ) (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) (B : ℝ) (hB : 0 ≤ B) :
    Tendsto (fun i ↦ ∫⁻ x, ENNReal.ofReal (min (h x) B) ∂(μ i : Measure X)) L
      (𝓝 (∫⁻ x, ENNReal.ofReal (min (h x) B) ∂(ν : Measure X))) := by
  let Ψ := truncateTest h hc h0 B hB
  have he := ENNReal.tendsto_ofReal
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak Ψ)
  have hp (ρ : ProbabilityMeasure X) : ENNReal.ofReal (∫ x, Ψ x ∂(ρ : Measure X)) =
      ∫⁻ x, ENNReal.ofReal (min (h x) B) ∂(ρ : Measure X) := by
    exact ofReal_integral_eq_lintegral_ofReal (Ψ.integrable _)
      (ae_of_all _ (truncateTest_nonneg h hc h0 B hB))
  simpa only [hp] using he

theorem iSup_integer_truncation (x : ℝ≥0∞) : (⨆ n : ℕ, min x (n : ℝ≥0∞)) = x := by
  calc
    _ = min x (⨆ n : ℕ, (n : ℝ≥0∞)) := (inf_iSup_eq x _).symm
    _ = x := by rw [ENNReal.iSup_natCast]; exact min_eq_left le_top

theorem lintegral_eq_iSup_truncations (ρ : Measure X) (h : X → ℝ) (hc : Continuous h) :
    (∫⁻ x, ENNReal.ofReal (h x) ∂ρ) =
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (h x) (n : ℝ)) ∂ρ := by
  simp_rw [ENNReal.ofReal_min,ENNReal.ofReal_natCast]
  calc
    _ = ∫⁻ x, ⨆ n : ℕ, min (ENNReal.ofReal (h x)) (n : ℝ≥0∞) ∂ρ :=
      lintegral_congr (fun x ↦ (iSup_integer_truncation _).symm)
    _ = _ := lintegral_iSup (fun n ↦ hc.measurable.ennreal_ofReal.min measurable_const)
      (fun n m hnm x ↦ min_le_min_left _ (Nat.cast_le.mpr hnm))

theorem target_lintegral_le_of_eventual_bound {ι : Type*} {L : Filter ι} [L.NeBot]
    (μ : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X) (hweak : Tendsto μ L (𝓝 ν))
    (h : X → ℝ) (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) (C : ℝ≥0∞)
    (hactual : ∀ᶠ i in L, (∫⁻ x, ENNReal.ofReal (h x) ∂(μ i : Measure X)) ≤ C) :
    (∫⁻ x, ENNReal.ofReal (h x) ∂(ν : Measure X)) ≤ C := by
  rw [lintegral_eq_iSup_truncations _ h hc]
  apply iSup_le
  intro n
  apply le_of_tendsto (truncate_lintegral_tendsto μ ν hweak h hc h0 n (Nat.cast_nonneg n))
  filter_upwards [hactual] with i hi
  exact (lintegral_mono (fun x ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _))).trans hi

theorem nonnegative_le_truncate_add_square (x B : ℝ) (hx : 0 ≤ x) (hB : 0 < B) :
    x ≤ min x B+(1/B)*x^2 := by
  by_cases hxb : x ≤ B
  · rw [min_eq_left hxb]
    exact le_add_of_nonneg_right (by positivity)
  · have hb : B ≤ x := (lt_of_not_ge hxb).le
    have hh : x ≤ x^2/B := (le_div_iff₀ hB).mpr (by nlinarith [mul_le_mul_of_nonneg_left hb hx])
    rw [min_eq_right hb]
    calc
      _ ≤ x^2/B := hh
      _ ≤ B+x^2/B := le_add_of_nonneg_left hB.le
      _ = _ := by ring

theorem lintegral_le_truncate_add_square_bound (ρ : Measure X) (h : X → ℝ)
    (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) (B : ℝ) (hB : 0 < B) (C : ℝ) (_hC : 0 ≤ C)
    (hsquare : (∫⁻ x, ENNReal.ofReal (h x^2) ∂ρ) ≤ ENNReal.ofReal C) :
    (∫⁻ x, ENNReal.ofReal (h x) ∂ρ) ≤
      (∫⁻ x, ENNReal.ofReal (min (h x) B) ∂ρ)+ENNReal.ofReal (C/B) := by
  have hb (x : X) : ENNReal.ofReal (h x) ≤ ENNReal.ofReal (min (h x) B)+
      ENNReal.ofReal (1/B)*ENNReal.ofReal (h x^2) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 : ℝ)/B),
      ← ENNReal.ofReal_add (le_min (h0 x) hB.le) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (nonnegative_le_truncate_add_square _ _ (h0 x) hB)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (min (h x) B)+
        ENNReal.ofReal (1/B)*ENNReal.ofReal (h x^2) ∂ρ := lintegral_mono hb
    _ = (∫⁻ x, ENNReal.ofReal (min (h x) B) ∂ρ)+
        ENNReal.ofReal (1/B)*(∫⁻ x, ENNReal.ofReal (h x^2) ∂ρ) := by
      rw [lintegral_add_left (hc.measurable.min measurable_const).ennreal_ofReal,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ (∫⁻ x, ENNReal.ofReal (min (h x) B) ∂ρ)+
        ENNReal.ofReal (1/B)*ENNReal.ofReal C := add_le_add le_rfl (mul_le_mul' le_rfl hsquare)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 : ℝ)/B)]; congr 2; ring

theorem target_lintegral_eq_of_square_bound_and_actual_limit {ι : Type*} {L : Filter ι} [L.NeBot]
    (μ : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X) (hweak : Tendsto μ L (𝓝 ν))
    (h : X → ℝ) (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) (C : ℝ) (hC : 0 ≤ C)
    (hsquare : ∀ᶠ i in L, (∫⁻ x, ENNReal.ofReal (h x^2) ∂(μ i : Measure X)) ≤ ENNReal.ofReal C)
    (K : ℝ≥0∞) (hactual : Tendsto (fun i ↦ ∫⁻ x, ENNReal.ofReal (h x) ∂(μ i : Measure X)) L (𝓝 K)) :
    (∫⁻ x, ENNReal.ofReal (h x) ∂(ν : Measure X)) = K := by
  apply le_antisymm
  · rw [lintegral_eq_iSup_truncations _ h hc]
    apply iSup_le
    intro n
    exact le_of_tendsto_of_tendsto
      (truncate_lintegral_tendsto μ ν hweak h hc h0 n (Nat.cast_nonneg n)) hactual
      (Eventually.of_forall (fun i ↦ lintegral_mono (fun x ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _))))
  · have hN (n : ℕ) : K ≤ (∫⁻ x, ENNReal.ofReal (h x) ∂(ν : Measure X))+
        ENNReal.ofReal (C/((n : ℝ)+1)) := by
      have hB : 0 < (n : ℝ)+1 := by positivity
      have he := (truncate_lintegral_tendsto μ ν hweak h hc h0 ((n : ℝ)+1) hB.le).add
        (tendsto_const_nhds (x := ENNReal.ofReal (C/((n : ℝ)+1))))
      apply le_trans (le_of_tendsto_of_tendsto hactual he ?_)
        (add_le_add (lintegral_mono (fun x ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _))) le_rfl)
      filter_upwards [hsquare] with i hi
      exact lintegral_le_truncate_add_square_bound _ h hc h0 _ hB C hC hi
    have hz : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C/((n : ℝ)+1))) atTop (𝓝 0) := by
      have hr := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C)
      simpa only [mul_zero,ENNReal.ofReal_zero,mul_one_div] using hr
    have he := (tendsto_const_nhds (x := ∫⁻ x, ENNReal.ofReal (h x) ∂(ν : Measure X))).add hz
    simp only [add_zero] at he
    exact ge_of_tendsto he (Eventually.of_forall hN)

theorem target_integrable_of_square_bound_and_actual_limit {ι : Type*} {L : Filter ι} [L.NeBot]
    (μ : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X) (hweak : Tendsto μ L (𝓝 ν))
    (h : X → ℝ) (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) (C : ℝ) (hC : 0 ≤ C)
    (hsquare : ∀ᶠ i in L, (∫⁻ x, ENNReal.ofReal (h x^2) ∂(μ i : Measure X)) ≤ ENNReal.ofReal C)
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (hactual : Tendsto (fun i ↦ ∫⁻ x, ENNReal.ofReal (h x) ∂(μ i : Measure X)) L (𝓝 K)) :
    Integrable h (ν : Measure X) := by
  refine ⟨hc.measurable.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)).mpr
  rw [target_lintegral_eq_of_square_bound_and_actual_limit μ ν hweak h hc h0 C hC hsquare K hactual]
  exact hK.lt_top

end PerronWright.WeakContinuousMomentIdentification
