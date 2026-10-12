import PerronWright.Probability.BrownianPositiveBridgeGlobalIncrementMoments
import PerronWright.Probability.FourthMomentDyadicModulus

/-! # Actual positive bridges have uniform all-level dyadic tail bounds

The samples use the literal clamped time `min(k/2^n,T)`. The input to
the generic proved fourth-moment mechanism is established here from the
actual conditioned bridge's endpoint-inclusive increment theorem. There
is no moment, modulus or tightness premise in the model terminal.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeDyadicModulus

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeGlobalIncrementMoments
open BrownianDyadicModulus

def clippedTime (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := min (DyadicFloorGeometry.coordinate n k) T

def samples (T : ℝ≥0) (n k : ℕ) (g : Path) : ℝ := g (clippedTime T n k)

def momentCoefficient (T : ℝ≥0) : ℝ := (globalCoefficient T).toReal

def badPaths (T : ℝ≥0) (M : ℕ) (R : ℝ) : Set Path :=
  ⋃ n, FourthMomentDyadicModulus.badLevel (samples T) M n R

theorem measurable_samples (T : ℝ≥0) (n k : ℕ) : Measurable (samples T n k) :=
  (continuous_eval (clippedTime T n k)).measurable

theorem measurableSet_badPaths (T : ℝ≥0) (M : ℕ) (R : ℝ) : MeasurableSet (badPaths T M R) :=
  MeasurableSet.iUnion (fun n ↦ FourthMomentDyadicModulus.measurableSet_badLevel (samples T) (measurable_samples T) M n R)

theorem momentCoefficient_nonneg (T : ℝ≥0) : 0 ≤ momentCoefficient T := ENNReal.toReal_nonneg

theorem ofReal_momentCoefficient (T : ℝ≥0) (hT : 0 < T) :
    ENNReal.ofReal (momentCoefficient T) = globalCoefficient T :=
  ENNReal.ofReal_toReal (globalCoefficient_ne_top T hT)

theorem clippedTime_compatible (T : ℝ≥0) (n k : ℕ) :
    clippedTime T (n+1) (2*k) = clippedTime T n k := by
  unfold clippedTime
  rw [DyadicFloorGeometry.coordinate_succ_even]

theorem clippedTime_adjacent_gap (T : ℝ≥0) (n k : ℕ) :
    |((clippedTime T n (k+1) : ℝ)-(clippedTime T n k : ℝ))| ≤ 1/(2 : ℝ)^n := by
  have hkR : (DyadicFloorGeometry.coordinate n k : ℝ) ≤ DyadicFloorGeometry.coordinate n (k+1) := by
    rw [DyadicFloorGeometry.coordinate_real,DyadicFloorGeometry.coordinate_real]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (by positivity)
  have hk : DyadicFloorGeometry.coordinate n k ≤ DyadicFloorGeometry.coordinate n (k+1) := hkR
  have hclip : clippedTime T n k ≤ clippedTime T n (k+1) := min_le_min hk le_rfl
  rw [abs_of_nonneg (sub_nonneg.mpr (show (clippedTime T n k : ℝ) ≤ clippedTime T n (k+1) from hclip))]
  unfold clippedTime
  by_cases ht : T ≤ DyadicFloorGeometry.coordinate n k
  · rw [min_eq_right ht,min_eq_right (ht.trans hk),sub_self]
    positivity
  · have hkT : DyadicFloorGeometry.coordinate n k ≤ T := (lt_of_not_ge ht).le
    rw [min_eq_left hkT]
    have hmin : (min (DyadicFloorGeometry.coordinate n (k+1)) T : ℝ) ≤
        DyadicFloorGeometry.coordinate n (k+1) := min_le_left _ _
    have hgap : (DyadicFloorGeometry.coordinate n (k+1) : ℝ)-DyadicFloorGeometry.coordinate n k = 1/(2 : ℝ)^n := by
      rw [DyadicFloorGeometry.coordinate_real,DyadicFloorGeometry.coordinate_real]
      push_cast
      ring
    rw [NNReal.coe_min]
    linarith

theorem eventually_uniform_adjacent_fourth (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ n k : ℕ,
      (∫⁻ g, ENNReal.ofReal (‖FourthMomentDyadicModulus.increment (samples T) n k g‖^4)
        ∂positiveBridgeLaw a T) ≤ ENNReal.ofReal (momentCoefficient T*(1/(2 : ℝ)^n)^2) := by
  filter_upwards [eventually_uniform_pair_fourth_increment T hT] with a ha
  intro n k
  have he := ha (clippedTime T n k) (clippedTime T n (k+1)) (min_le_right _ _) (min_le_right _ _)
  change (∫⁻ g, ENNReal.ofReal (‖g (clippedTime T n (k+1))-g (clippedTime T n k)‖^4) ∂positiveBridgeLaw a T) ≤ _
  calc
    _ ≤ globalCoefficient T*ENNReal.ofReal (|((clippedTime T n (k+1) : ℝ)-(clippedTime T n k : ℝ))|^2) := he
    _ ≤ globalCoefficient T*ENNReal.ofReal ((1/(2 : ℝ)^n)^2) := mul_le_mul' le_rfl
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (clippedTime_adjacent_gap T n k) 2))
    _ = _ := by rw [ENNReal.ofReal_mul (momentCoefficient_nonneg T),ofReal_momentCoefficient T hT]

theorem eventually_uniform_allLevel_bad_measure_bound (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (M : ℕ) (R : ℝ), 0 < R →
      positiveBridgeLaw a T (badPaths T M R) ≤
        ENNReal.ofReal ((momentCoefficient T*(M : ℝ)/R^4)/(1-tailRatio)) := by
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_adjacent_fourth T hT] with a ha h4
  intro M R hR
  let : IsProbabilityMeasure (positiveBridgeLaw a T) := positiveBridgeLaw_isProbability a ha T hT
  exact FourthMomentDyadicModulus.allLevel_bad_measure_bound (positiveBridgeLaw a T) (samples T)
    (measurable_samples T) (momentCoefficient T) (momentCoefficient_nonneg T) h4 M hR

theorem eventually_ae_localBound (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ g ∂positiveBridgeLaw a T,
      DyadicGeometricApproximation.LocalBound (fun n k ↦ samples T n k g) := by
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_adjacent_fourth T hT] with a ha h4
  let : IsProbabilityMeasure (positiveBridgeLaw a T) := positiveBridgeLaw_isProbability a ha T hT
  exact FourthMomentDyadicModulus.ae_localBound (positiveBridgeLaw a T) (samples T)
    (measurable_samples T) (momentCoefficient T) (momentCoefficient_nonneg T) h4

end PerronWright.BrownianPositiveBridgeDyadicModulus
