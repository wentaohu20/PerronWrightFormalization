import PerronWright.Probability.BrownianKilledAreaMomentRecursion
import PerronWright.Probability.BrownianPositiveKilledKernel

/-! # Literal time/state area-moment density recursion

The base is the actual absorbing-zero Gaussian difference. Each higher
order is the nonnegative time/state insertion of the previous density.
Joint measurability is proved before these are used to identify actual
Brownian moment measures; no density identity is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentDensity

open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel

abbrev Parameters := ℝ≥0 × (ℝ × ℝ)

theorem measurable_time_joint_density :
    Measurable (fun p : Parameters ↦ BrownianPositiveKilledEndpoint.density p.2.1 p.1 p.2.2) := by
  have hp : Measurable (fun p : Parameters ↦ gaussianPDFReal p.2.1 p.1 p.2.2) :=
    measurable_uncurry_gaussianPDFReal.comp
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hn : Measurable (fun p : Parameters ↦ gaussianPDFReal (-p.2.1) p.1 p.2.2) :=
    measurable_uncurry_gaussianPDFReal.comp
      ((measurable_fst.comp measurable_snd).neg.prodMk
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  change Measurable (fun p : Parameters ↦ ENNReal.ofReal
    (if 0 < p.2.2 then gaussianPDFReal p.2.1 p.1 p.2.2-gaussianPDFReal (-p.2.1) p.1 p.2.2 else 0))
  exact (Measurable.ite
    (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))
    (hp.sub hn) measurable_const).ennreal_ofReal

def density : ℕ → Parameters → ℝ≥0∞
  | 0,p => BrownianPositiveKilledEndpoint.density p.2.1 p.1 p.2.2
  | n+1,p => ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ q : ℝ × ℝ,
      (Ioo (0 : ℝ) (p.1 : ℝ)).indicator
        (fun r : ℝ ↦ BrownianPositiveKilledEndpoint.density p.2.1 (Real.toNNReal r) q.2*
          ENNReal.ofReal q.2*density n (p.1-Real.toNNReal r,(q.2,p.2.2))) q.1

theorem measurable_step_integrand {D : Parameters → ℝ≥0∞} (hD : Measurable D) :
    Measurable (fun p : Parameters × (ℝ × ℝ) ↦
      (Ioo (0 : ℝ) (p.1.1 : ℝ)).indicator
        (fun r : ℝ ↦ BrownianPositiveKilledEndpoint.density p.1.2.1 (Real.toNNReal r) p.2.2*
          ENNReal.ofReal p.2.2*D (p.1.1-Real.toNNReal r,(p.2.2,p.1.2.2))) p.2.1) := by
  have hs : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ Real.toNNReal p.2.1) :=
    continuous_real_toNNReal.measurable.comp (measurable_fst.comp measurable_snd)
  have hT : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ p.1.1) :=
    measurable_fst.comp measurable_fst
  have hx : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ p.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hy : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hz : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ p.2.2) :=
    measurable_snd.comp measurable_snd
  have hr : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ p.2.1) :=
    measurable_fst.comp measurable_snd
  simp only [Set.indicator,mem_Ioo]
  exact Measurable.ite ((measurableSet_lt measurable_const hr).inter
    (measurableSet_lt hr (NNReal.continuous_coe.measurable.comp hT)))
    (((measurable_time_joint_density.comp (hs.prodMk (hx.prodMk hz))).mul
      hz.ennreal_ofReal).mul (hD.comp ((hT.sub hs).prodMk (hz.prodMk hy)))) measurable_const

theorem measurable_density (n : ℕ) : Measurable (density n) := by
  induction n with
  | zero => exact measurable_time_joint_density
  | succ n ih =>
    exact measurable_const.mul ((measurable_step_integrand ih).lintegral_prod_right')

theorem measurable_density_state (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    Measurable (fun y : ℝ ↦ density n (T,(x,y))) :=
  (measurable_density n).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

@[simp] theorem density_zero (T : ℝ≥0) (x y : ℝ) :
    density 0 (T,(x,y)) = BrownianPositiveKilledEndpoint.density x T y := rfl

theorem density_succ (n : ℕ) (T : ℝ≥0) (x y : ℝ) :
    density (n+1) (T,(x,y)) = ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ r in Ioo 0 (T : ℝ),
      ∫⁻ z : ℝ, BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*
        ENNReal.ofReal z*density n (T-Real.toNNReal r,(z,y)) := by
  have hm : Measurable (fun q : ℝ × ℝ ↦
      (Ioo (0 : ℝ) (T : ℝ)).indicator
        (fun r : ℝ ↦ BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) q.2*
          ENNReal.ofReal q.2*density n (T-Real.toNNReal r,(q.2,y))) q.1) :=
    (measurable_step_integrand (measurable_density n)).comp
      (measurable_const.prodMk measurable_id : Measurable (fun q : ℝ × ℝ ↦ ((T,(x,y)),q)))
  rw [density,Measure.volume_eq_prod ℝ ℝ,lintegral_prod _ hm.aemeasurable]
  congr 1
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioo (0 : ℝ) T
  · simp only [indicator_of_mem hr]
  · simp only [indicator_of_notMem hr,lintegral_zero]

end PerronWright.BrownianKilledAreaMomentDensity
