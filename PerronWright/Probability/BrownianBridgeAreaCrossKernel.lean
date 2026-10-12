import PerronWright.Probability.BrownianPinnedBridgeAreaTilt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Computed bridge--area cross kernel

Finite cross covariances and their limits are calculated from the
actual pinned Brownian covariance. No continuous-area covariance is
used as an assumption. The signed bridge remains distinct from a
positive excursion.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeAreaCrossKernel

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeFiniteLaw
open BrownianPinnedBridgeArea BrownianUniformQuadrature

def crossKernel (T t : ℝ≥0) (s : ℝ) : ℝ := min (t : ℝ) s-(t : ℝ)*s/(T : ℝ)

def crossMean (T t : ℝ≥0) : ℝ := (t : ℝ)*((T : ℝ)-(t : ℝ))/2

theorem continuous_crossKernel (T t : ℝ≥0) : Continuous (crossKernel T t) := by
  unfold crossKernel
  fun_prop

theorem integral_crossKernel (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) :
    (∫ s in 0..(T : ℝ), crossKernel T t s) = crossMean T t := by
  have hmin : (∫ s in 0..(T : ℝ), min (t : ℝ) s) = (t : ℝ)*(T : ℝ)-(t : ℝ)^2/2 := by
    have hg : Continuous (fun s : ℝ ↦ min (t : ℝ) s) := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable 0 (t : ℝ)) (hg.intervalIntegrable (t : ℝ) (T : ℝ))]
    have hl : (∫ s in 0..(t : ℝ), min (t : ℝ) s) = ∫ s in 0..(t : ℝ), s :=
      intervalIntegral.integral_congr (fun s hs ↦ min_eq_right
        ((by simpa only [uIcc_of_le (show (0 : ℝ) ≤ t from t.property)] using hs :
          s ∈ Icc 0 (t : ℝ)).2))
    have hr : (∫ s in (t : ℝ)..(T : ℝ), min (t : ℝ) s) =
        ∫ _ in (t : ℝ)..(T : ℝ), (t : ℝ) :=
      intervalIntegral.integral_congr (fun s hs ↦ min_eq_left
        ((by simpa only [uIcc_of_le (show (t : ℝ) ≤ T from ht)] using hs :
          s ∈ Icc (t : ℝ) (T : ℝ)).1))
    rw [hl,hr,integral_id,intervalIntegral.integral_const]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero,smul_eq_mul]
    ring
  unfold crossKernel
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous (fun s : ℝ ↦ min (t : ℝ) s)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun s : ℝ ↦ (t : ℝ)*s/(T : ℝ))).intervalIntegrable _ _),
    hmin,intervalIntegral.integral_div,intervalIntegral.integral_const_mul,integral_id]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero,crossMean]
  have hne : (T : ℝ) ≠ 0 := ne_of_gt (show 0 < (T : ℝ) from hT)
  field_simp
  ring

theorem covariance_bridge_quadrature (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) (m : ℕ) :
    cov[bridge T t,quadrature T m;pathLaw] = leftSum (T : ℝ) m (crossKernel T t) := by
  unfold quadrature linearTest
  rw [covariance_fun_sum_right
    (fun i ↦ (bridge_hasGaussianLaw T (timeGrid T m i)).memLp_two.const_mul _)
    (bridge_hasGaussianLaw T t).memLp_two]
  simp only [covariance_const_mul_right,covariance_bridge T _ _ hT ht (timeGrid_le T m _),
    timeGrid_real]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦
    (T : ℝ)/(m : ℝ)*
      (min (t : ℝ) (grid (T : ℝ) m i)-(t : ℝ)*grid (T : ℝ) m i/(T : ℝ)))]
  rfl

theorem covariance_bridge_quadrature_tendsto (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) :
    Tendsto (fun n : ℕ ↦ cov[bridge T t,quadrature T (n+1);pathLaw])
      atTop (𝓝 (crossMean T t)) := by
  simp only [covariance_bridge_quadrature T t hT ht]
  rw [← integral_crossKernel T t hT ht]
  exact leftSum_tendsto_integral (T : ℝ) T.property _ (continuous_crossKernel T t)

variable {ι : Type*} [Fintype ι]

def testCrossMean (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) : ℝ := ∑ i, c i*crossMean T (t i)

theorem covariance_linearTest_quadrature (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) (m : ℕ) :
    cov[linearTest T t c,quadrature T m;pathLaw] =
      ∑ i, c i*cov[bridge T (t i),quadrature T m;pathLaw] := by
  unfold linearTest
  have hterm (i : ι) : MemLp (fun f ↦ c i*bridge T (t i) f) 2 pathLaw :=
    (bridge_hasGaussianLaw T (t i)).memLp_two.const_mul _
  have hq : MemLp (quadrature T m) 2 pathLaw :=
    (hasGaussianLaw_linearTest T (timeGrid T m) _).memLp_two
  rw [covariance_fun_sum_left hterm hq]
  simp only [covariance_const_mul_left]

theorem covariance_linearTest_quadrature_tendsto (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) :
    Tendsto (fun n : ℕ ↦ cov[linearTest T t c,quadrature T (n+1);pathLaw])
      atTop (𝓝 (testCrossMean T t c)) := by
  simp only [covariance_linearTest_quadrature,testCrossMean]
  exact tendsto_finsetSum _ (fun i _ ↦
    (covariance_bridge_quadrature_tendsto T (t i) hT (ht i)).const_mul (c i))

end PerronWright.BrownianBridgeAreaCrossKernel
