import PerronWright.Probability.BrownianKilledAreaSemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Literal integral calculus for killed-area weights

Finite path quadratures give joint time/path measurability of the actual
area. The fundamental theorem of calculus then gives its derivative and
the exact exponential depletion identity. These are deterministic path
facts, not an assumed stochastic differential or Feynman--Kac identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaDuhamelGeometry

open BrownianPathLaw BrownianUniformQuadrature BrownianBridgeCyclicArea
open BrownianPathIndependentIncrements ContinuousPathReflection ContinuousPathFirstPassage
open BrownianKilledAreaGeometry

theorem continuous_joint_pathQuadrature (m : ℕ) :
    Continuous (fun p : ℝ≥0 × Path ↦ pathQuadrature p.1 m p.2) := by
  unfold pathQuadrature leftSum
  apply continuous_finsetSum
  intro i _hi
  have hc : Continuous (fun p : ℝ≥0 × Path ↦ grid (p.1 : ℝ) m i) := by
    unfold grid
    fun_prop
  have ht : Continuous (fun p : ℝ≥0 × Path ↦ (p.1 : ℝ)/(m : ℝ)) := by fun_prop
  exact ht.mul (continuous_joint_eval.comp
    (continuous_snd.prodMk (continuous_real_toNNReal.comp hc)))

theorem measurable_joint_pathArea :
    Measurable (fun p : ℝ≥0 × Path ↦ pathArea p.1 p.2) :=
  measurable_of_tendsto_metrizable
    (fun n ↦ (continuous_joint_pathQuadrature (n+1)).measurable)
    (tendsto_pi_nhds.mpr (fun p ↦ pathQuadrature_tendsto_pathArea p.1 p.2))

theorem continuous_time_futurePath :
    Continuous (fun p : ℝ≥0 × Path ↦ futurePath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_fst.snd).eval (continuous_fst.fst.add continuous_snd)).sub
    ((continuous_fst.snd).eval continuous_fst.fst)

theorem measurable_time_state_shiftedArea (level : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℝ × Path) ↦ shiftedArea level p.2.1 p.1 p.2.2) :=
  ((NNReal.continuous_coe.measurable.comp measurable_fst).mul
    ((measurable_fst.comp measurable_snd).sub_const level)).add
    (measurable_joint_pathArea.comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

theorem measurable_time_state_weight (level : ℝ) (u : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℝ × Path) ↦
      BrownianKilledAreaKernel.weight level u p.1 p.2.1 p.2.2) := by
  have hs : MeasurableSet {p : ℝ≥0 × (ℝ × Path) | p.2.2 ∈ survival (level-p.2.1) p.1} :=
    (isOpen_lt (continuous_const.sub continuous_snd.fst)
      (BrownianPathReflectionLaw.continuous_joint_minimum.comp
        (continuous_snd.snd.prodMk continuous_fst))).measurableSet
  change Measurable (fun p : ℝ≥0 × (ℝ × Path) ↦ if p.2.2 ∈ survival (level-p.2.1) p.1 then
    ENNReal.ofReal (Real.exp (-(u : ℝ)*shiftedArea level p.2.1 p.1 p.2.2)) else 0)
  exact Measurable.ite hs
    ((measurable_const.mul (measurable_time_state_shiftedArea level)).exp.ennreal_ofReal)
    measurable_const

def realArea (level x : ℝ) (f : Path) (r : ℝ) : ℝ :=
  r*(x-level)+∫ v in (0 : ℝ)..r, f (Real.toNNReal v)

theorem realArea_at_nonnegative (level x : ℝ) (f : Path) (t : ℝ≥0) :
    realArea level x f t = shiftedArea level x t f := rfl

theorem realArea_hasDerivAt (level x : ℝ) (f : Path) (r : ℝ) :
    HasDerivAt (realArea level x f) (x-level+f (Real.toNNReal r)) r := by
  have hc : Continuous (fun v : ℝ ↦ f (Real.toNNReal v)) :=
    (continuous_path f).comp continuous_real_toNNReal
  have hi : HasDerivAt (fun v : ℝ ↦ ∫ z in (0 : ℝ)..v, f (Real.toNNReal z))
      (f (Real.toNNReal r)) r :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  change HasDerivAt (fun v : ℝ ↦ v*(x-level)+∫ z in (0 : ℝ)..v, f (Real.toNNReal z))
    (x-level+f (Real.toNNReal r)) r
  convert! ((hasDerivAt_id r).mul_const (x-level)).add hi using 1
  simp

theorem continuous_realArea (level x : ℝ) (f : Path) : Continuous (realArea level x f) :=
  continuous_iff_continuousAt.mpr (fun r ↦ (realArea_hasDerivAt level x f r).continuousAt)

theorem exp_realArea_hasDerivAt (level x u : ℝ) (f : Path) (r : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (-u*realArea level x f v))
      (-u*((x-level+f (Real.toNNReal r))*Real.exp (-u*realArea level x f r))) r := by
  apply ((realArea_hasDerivAt level x f r).const_mul (-u)).exp.congr_deriv
  ring

theorem exp_area_depletion (level x u : ℝ) (t : ℝ≥0) (f : Path) :
    1-Real.exp (-u*shiftedArea level x t f) =
      u*∫ r in (0 : ℝ)..(t : ℝ),
        (x-level+f (Real.toNNReal r))*Real.exp (-u*realArea level x f r) := by
  have hc : Continuous (fun r : ℝ ↦
      (x-level+f (Real.toNNReal r))*Real.exp (-u*realArea level x f r)) :=
    (continuous_const.add ((continuous_path f).comp continuous_real_toNNReal)).mul
      (Real.continuous_exp.comp ((continuous_realArea level x f).const_mul (-u)))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _hr ↦ exp_realArea_hasDerivAt level x u f r)
    ((hc.const_mul (-u)).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul,realArea_at_nonnegative,
    show realArea level x f 0 = 0 by simp [realArea],mul_zero,Real.exp_zero] at he
  linarith

end PerronWright.BrownianKilledAreaDuhamelGeometry
