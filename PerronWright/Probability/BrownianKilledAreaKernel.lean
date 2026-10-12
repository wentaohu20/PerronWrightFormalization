import PerronWright.Probability.BrownianKilledAreaGeometry
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Genuine surviving Brownian area-weighted transition kernel

The weight uses the literal integral of the path above the absorbing
boundary. The finite measure is defined from the actual Brownian path
law, not from an assumed differential equation or Feynman--Kac formula.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaKernel

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianKilledAreaGeometry BrownianKilledSemigroup

def weight (level : ℝ) (u : ℝ≥0) (t : ℝ≥0) (x : ℝ) (f : Path) : ℝ≥0∞ :=
  (survival (level-x) t).indicator
    (fun g ↦ ENNReal.ofReal (Real.exp (-(u : ℝ)*shiftedArea level x t g))) f

theorem measurable_joint_weight (level : ℝ) (u t : ℝ≥0) :
    Measurable (fun p : ℝ × Path ↦ weight level u t p.1 p.2) := by
  change Measurable (fun p : ℝ × Path ↦ if p.2 ∈ survival (level-p.1) t then
    ENNReal.ofReal (Real.exp (-(u : ℝ)*shiftedArea level p.1 t p.2)) else 0)
  have hs : MeasurableSet {p : ℝ × Path | p.2 ∈ survival (level-p.1) t} :=
    (isOpen_lt (continuous_const.sub continuous_fst)
      ((continuous_minimum_at t).comp continuous_snd)).measurableSet
  exact Measurable.ite hs
    ((measurable_const.mul (measurable_joint_shiftedArea level t)).exp.ennreal_ofReal)
    measurable_const

theorem measurable_weight (level : ℝ) (u t : ℝ≥0) (x : ℝ) :
    Measurable (weight level u t x) :=
  (measurable_joint_weight level u t).comp (measurable_const.prodMk measurable_id)

theorem weight_le_one (level : ℝ) (u t : ℝ≥0) (x : ℝ) (f : Path) :
    weight level u t x f ≤ 1 := by
  by_cases hf : f ∈ survival (level-x) t
  · rw [weight,indicator_of_mem hf]
    exact (ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr u.coe_nonneg)
        (shiftedArea_nonneg_of_survival level x t f hf)))).trans_eq ENNReal.ofReal_one
  · simp only [weight,indicator_of_notMem hf,zero_le]

theorem weight_past (level : ℝ) (u t : ℝ≥0) (x : ℝ) (f : Path) :
    weight level u t x (pastPath t f) = weight level u t x f := by
  by_cases hf : f ∈ survival (level-x) t
  · have hp := (past_survival_iff (level-x) t f).mpr hf
    rw [weight,weight,indicator_of_mem hp,indicator_of_mem hf,shiftedArea_past]
  · have hp := (past_survival_iff (level-x) t f).not.mpr hf
    simp only [weight,indicator_of_notMem hp,indicator_of_notMem hf]

theorem weight_add (level : ℝ) (u s t : ℝ≥0) (x : ℝ) (f : Path) :
    weight level u (s+t) x f =
      weight level u s x f*weight level u t (x+f s) (futurePath s f) := by
  have hl : level-x-f s = level-(x+f s) := by ring
  by_cases hs : f ∈ survival (level-x) s
  · by_cases ht : futurePath s f ∈ survival (level-(x+f s)) t
    · have hst := (survival_add_iff (level-x) s t f).mpr ⟨hs,by simpa only [hl] using ht⟩
      rw [weight,weight,weight,indicator_of_mem hs,indicator_of_mem ht,indicator_of_mem hst,
        shiftedArea_add]
      rw [show -(u : ℝ)*(shiftedArea level x s f+
        shiftedArea level (x+f s) t (futurePath s f)) =
        -(u : ℝ)*shiftedArea level x s f+
        -(u : ℝ)*shiftedArea level (x+f s) t (futurePath s f) by ring,
        Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    · have hst : f ∉ survival (level-x) (s+t) := by
        intro hf
        exact ht (by simpa only [hl] using ((survival_add_iff (level-x) s t f).mp hf).2)
      simp only [weight,indicator_of_notMem hst,indicator_of_notMem ht,mul_zero]
  · have hst : f ∉ survival (level-x) (s+t) :=
      fun hf ↦ hs ((survival_add_iff (level-x) s t f).mp hf).1
    simp only [weight,indicator_of_notMem hst,indicator_of_notMem hs,zero_mul]

def law (level : ℝ) (u t : ℝ≥0) (x : ℝ) : Measure ℝ :=
  (pathLaw.withDensity (weight level u t x)).map (fun f : Path ↦ x+f t)

theorem withDensity_weight_isFinite (level : ℝ) (u t : ℝ≥0) (x : ℝ) :
    IsFiniteMeasure (pathLaw.withDensity (weight level u t x)) := by
  apply isFiniteMeasure_withDensity
  apply ne_top_of_le_ne_top (show (∫⁻ _f : Path, (1 : ℝ≥0∞) ∂pathLaw) ≠ ∞ by simp)
  exact lintegral_mono (weight_le_one level u t x)

instance law_isFinite (level : ℝ) (u t : ℝ≥0) (x : ℝ) : IsFiniteMeasure (law level u t x) := by
  let := withDensity_weight_isFinite level u t x
  unfold law
  infer_instance

theorem law_lintegral (level : ℝ) (u t : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂law level u t x) =
      ∫⁻ f, weight level u t x f*F (x+f t) ∂pathLaw := by
  have hm : Measurable (fun f : Path ↦ x+f t) :=
    measurable_const.add (continuous_eval t).measurable
  rw [law,lintegral_map hF hm]
  exact lintegral_withDensity_eq_lintegral_mul pathLaw (measurable_weight level u t x) (hF.comp hm)

theorem measurable_law_lintegral (level : ℝ) (u t : ℝ≥0)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun x : ℝ ↦ ∫⁻ y, F y ∂law level u t x) := by
  have hm : Measurable (fun p : ℝ × Path ↦ weight level u t p.1 p.2*F (p.1+p.2 t)) :=
    (measurable_joint_weight level u t).mul (hF.comp
      (measurable_fst.add ((continuous_eval t).measurable.comp measurable_snd)))
  have he : (fun x : ℝ ↦ ∫⁻ y, F y ∂law level u t x) =
      (fun x : ℝ ↦ ∫⁻ f, weight level u t x f*F (x+f t) ∂pathLaw) :=
    funext (fun x ↦ law_lintegral level u t x hF)
  rw [he]
  exact hm.lintegral_prod_right'

theorem measurable_law_apply (level : ℝ) (u t : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) : Measurable (fun x : ℝ ↦ law level u t x B) := by
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using
    measurable_law_lintegral level u t (measurable_const.indicator hB :
      Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))

theorem law_univ_le_one (level : ℝ) (u t : ℝ≥0) (x : ℝ) : law level u t x univ ≤ 1 := by
  have he := law_lintegral level u t x (measurable_const : Measurable (fun _ : ℝ ↦ (1 : ℝ≥0∞)))
  simp only [lintegral_one,mul_one] at he
  rw [he]
  exact (lintegral_mono (weight_le_one level u t x)).trans_eq (by simp)

def areaKernel (level : ℝ) (u t : ℝ≥0) : Kernel ℝ ℝ :=
  ⟨law level u t,Measure.measurable_measure.mpr (fun _ hB ↦ measurable_law_apply level u t hB)⟩

@[simp] theorem areaKernel_apply (level : ℝ) (u t : ℝ≥0) (x : ℝ) :
    areaKernel level u t x = law level u t x := rfl

instance areaKernel_isFinite (level : ℝ) (u t : ℝ≥0) : IsFiniteKernel (areaKernel level u t) :=
  ⟨⟨1,ENNReal.one_lt_top,law_univ_le_one level u t⟩⟩

end PerronWright.BrownianKilledAreaKernel
