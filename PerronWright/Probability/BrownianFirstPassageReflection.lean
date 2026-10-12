import PerronWright.Probability.BrownianFirstPassageGridReflection
import PerronWright.Probability.DyadicFloorGeometry
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Genuine reflection at the bounded literal first passage

The actual finite-grid first-passage reflections converge in the genuine
locally uniform path topology. Deterministic mesh estimates prove this
for every continuous path. Bounded continuous tests and dominated
convergence therefore give law preservation by reflection at the
literal first passage capped at any finite real horizon. There is no
reflection-principle, strong-Markov, or passage-density premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageReflection

open BrownianPathLaw BrownianPathIndependentIncrements BrownianFiniteReflectionLaw
open ContinuousPathFirstPassage BrownianFirstPassageGridReflection

def cappedTime (level : ℝ) (T : ℝ≥0) (f : Path) : ℝ≥0 :=
  (min (firstPassage level f) (T : ℝ≥0∞)).toNNReal

theorem cappedTime_coe (level : ℝ) (T : ℝ≥0) (f : Path) :
    (cappedTime level T f : ℝ≥0∞) = min (firstPassage level f) (T : ℝ≥0∞) := by
  apply ENNReal.coe_toNNReal
  intro h
  have hb := min_le_right (firstPassage level f) (T : ℝ≥0∞)
  rw [h] at hb
  exact ENNReal.coe_ne_top (le_antisymm le_top hb)

theorem cappedTime_le (level : ℝ) (T : ℝ≥0) (f : Path) : cappedTime level T f ≤ T := by
  apply ENNReal.coe_le_coe.mp
  rw [cappedTime_coe]
  exact min_le_right _ _

theorem measurable_cappedTime (level : ℝ) (T : ℝ≥0) : Measurable (cappedTime level T) :=
  ((measurable_firstPassage level).min measurable_const).ennreal_toNNReal

theorem continuous_cappedTime_horizon (level : ℝ) (f : Path) :
    Continuous (fun T : ℝ≥0 ↦ cappedTime level T f) := by
  by_cases hτ : firstPassage level f = ⊤
  · have he : (fun T : ℝ≥0 ↦ cappedTime level T f) = id := by
      funext T
      simp only [cappedTime,hτ,min_top_left,ENNReal.toNNReal_coe,id_eq]
    rw [he]
    exact continuous_id
  · have he : (fun T : ℝ≥0 ↦ cappedTime level T f) =
        (fun T ↦ min (firstPassage level f).toNNReal T) := by
      funext T
      unfold cappedTime
      rw [← ENNReal.coe_toNNReal hτ,← ENNReal.coe_min,ENNReal.toNNReal_coe]
      simp only [ENNReal.toNNReal_coe]
    rw [he]
    exact continuous_const.min continuous_id

def selectedTime (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) : ℝ≥0 :=
  t (gridIndex level t m f)

theorem cappedTime_le_selectedTime (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) :
    cappedTime level (t m) f ≤ selectedTime level t m f := by
  let i := gridIndex level t m f
  have hi := (gridIndex_eq_iff level t m f i).mp rfl
  apply ENNReal.coe_le_coe.mp
  rw [cappedTime_coe]
  change min (firstPassage level f) (t m : ℝ≥0∞) ≤ t i
  rcases hi.1 with hcross | hlast
  · exact (min_le_left _ _).trans hcross
  · rw [hlast]
    exact min_le_right _ _

theorem selectedTime_le_cappedTime_add (level : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (hzero : t 0 = 0) (m : ℕ) (δ : ℝ≥0)
    (hstep : ∀ k < m, t (k+1) ≤ t k+δ) (f : Path) :
    selectedTime level t m f ≤ cappedTime level (t m) f+δ := by
  let i := gridIndex level t m f
  have hi := (gridIndex_eq_iff level t m f i).mp rfl
  change t i ≤ _
  by_cases hz : i.val = 0
  · rw [hz,hzero]
    exact zero_le
  · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hkm : k < m := by have h := i.isLt; omega
    have hprev : t k ≤ cappedTime level (t m) f := by
      apply ENNReal.coe_le_coe.mp
      rw [cappedTime_coe]
      exact le_min (hi.2 k (by omega)).le (ENNReal.coe_le_coe.mpr (ht (by omega)))
    rw [hk]
    exact (hstep k hkm).trans (add_le_add hprev le_rfl)

theorem dyadic_horizon_tendsto (T : ℝ≥0) :
    Tendsto (fun n ↦ dyadicGrid n (DyadicFloorGeometry.index n T)) atTop (𝓝 T) := by
  have hδ : Tendsto (fun n : ℕ ↦ (1 : ℝ)/(2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [div_pow,one_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)
  have hd : Tendsto (fun n ↦ (T : ℝ)-
      (dyadicGrid n (DyadicFloorGeometry.index n T) : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero _ _ hδ
    · intro n
      have h := DyadicFloorGeometry.index_le_scaled n T
      change 0 ≤ (T : ℝ)-(DyadicFloorGeometry.index n T : ℝ)/(2 : ℝ)^n
      exact sub_nonneg.mpr ((div_le_iff₀ (by positivity : 0 < (2 : ℝ)^n)).mpr h)
    · intro n
      have h := DyadicFloorGeometry.scaled_lt_index_add_one n T
      change (T : ℝ)-(DyadicFloorGeometry.index n T : ℝ)/(2 : ℝ)^n ≤ 1/(2 : ℝ)^n
      have hp : 0 < (2 : ℝ)^n := by positivity
      have hq := (lt_div_iff₀ hp).mpr h
      rw [add_div] at hq
      linarith
  apply NNReal.tendsto_coe.mp
  have hc : Tendsto (fun _ : ℕ ↦ (T : ℝ)) atTop (𝓝 (T : ℝ)) := tendsto_const_nhds
  simpa only [sub_sub_cancel,sub_zero] using hc.sub hd

theorem dyadic_selectedTime_tendsto (level : ℝ) (T : ℝ≥0) (f : Path) :
    Tendsto (fun n ↦ selectedTime level (dyadicGrid n) (DyadicFloorGeometry.index n T) f)
      atTop (𝓝 (cappedTime level T f)) := by
  have hδ : Tendsto (fun n : ℕ ↦ (1 : ℝ)/(2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [div_pow,one_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)
  have hd : Tendsto (fun n ↦
      (selectedTime level (dyadicGrid n) (DyadicFloorGeometry.index n T) f : ℝ)-
        (cappedTime level (dyadicGrid n (DyadicFloorGeometry.index n T)) f : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero _ _ hδ
    · intro n
      exact sub_nonneg.mpr (show
        (cappedTime level (dyadicGrid n (DyadicFloorGeometry.index n T)) f : ℝ) ≤
          selectedTime level (dyadicGrid n) (DyadicFloorGeometry.index n T) f from
        cappedTime_le_selectedTime level (dyadicGrid n) _ f)
    · intro n
      have h := selectedTime_le_cappedTime_add level (dyadicGrid n) (monotone_dyadicGrid n)
        (by simp [dyadicGrid]) (DyadicFloorGeometry.index n T) (1/(2 : ℝ≥0)^n)
        (by intro k hk; unfold dyadicGrid; rw [Nat.cast_add,Nat.cast_one,add_div]) f
      have hr : (selectedTime level (dyadicGrid n) (DyadicFloorGeometry.index n T) f : ℝ) ≤
          (cappedTime level (dyadicGrid n (DyadicFloorGeometry.index n T)) f : ℝ)+1/(2 : ℝ)^n := by
        exact_mod_cast h
      linarith
  have hc := NNReal.tendsto_coe.mpr
    (((continuous_cappedTime_horizon level f).tendsto T).comp (dyadic_horizon_tendsto T))
  apply NNReal.tendsto_coe.mp
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hd.add hc

def boundedReflection (level : ℝ) (T : ℝ≥0) (f : Path) : Path :=
  reflectionPath (cappedTime level T f) f

theorem measurable_boundedReflection (level : ℝ) (T : ℝ≥0) :
    Measurable (boundedReflection level T) :=
  continuous_joint_reflectionPath.measurable.comp
    ((measurable_cappedTime level T).prodMk measurable_id)

theorem dyadicReflection_tendsto (level : ℝ) (T : ℝ≥0) (f : Path) :
    Tendsto (fun n ↦ dyadicReflection level n (DyadicFloorGeometry.index n T) f)
      atTop (𝓝 (boundedReflection level T f)) := by
  have hc : Continuous (fun s : ℝ≥0 ↦ reflectionPath s f) :=
    continuous_joint_reflectionPath.comp (continuous_id.prodMk continuous_const)
  exact (hc.tendsto (cappedTime level T f)).comp (dyadic_selectedTime_tendsto level T f)

/-- Genuine Brownian path law preservation at the literal bounded first
passage, proved by finite-grid reflection and path-space convergence. -/
theorem boundedReflection_law (level : ℝ) (T : ℝ≥0) :
    pathLaw.map (boundedReflection level T) = pathLaw := by
  have : IsProbabilityMeasure (pathLaw.map (boundedReflection level T)) :=
    Measure.isProbabilityMeasure_map (measurable_boundedReflection level T).aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro Ψ
  rw [integral_map (measurable_boundedReflection level T).aemeasurable Ψ.continuous.measurable.aestronglyMeasurable]
  have hl : Tendsto (fun n ↦ ∫ f, Ψ (dyadicReflection level n (DyadicFloorGeometry.index n T) f) ∂pathLaw)
      atTop (𝓝 (∫ f, Ψ (boundedReflection level T f) ∂pathLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ ‖Ψ‖)
    · intro n
      exact (Ψ.continuous.measurable.comp (measurable_dyadicReflection _ _ _)).aestronglyMeasurable
    · exact integrable_const ‖Ψ‖
    · exact fun _ ↦ Eventually.of_forall (fun f ↦ Ψ.norm_coe_le_norm _)
    · exact Eventually.of_forall (fun f ↦ (Ψ.continuous.tendsto _).comp (dyadicReflection_tendsto level T f))
  have he (n : ℕ) : (∫ f, Ψ (dyadicReflection level n (DyadicFloorGeometry.index n T) f) ∂pathLaw) =
      ∫ f, Ψ f ∂pathLaw := by
    rw [← integral_map (measurable_dyadicReflection _ _ _).aemeasurable Ψ.continuous.measurable.aestronglyMeasurable,
      dyadicReflection_law]
  exact tendsto_nhds_unique hl (by simpa only [he] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ ∫ f, Ψ f ∂pathLaw) atTop (𝓝 (∫ f, Ψ f ∂pathLaw))))

end PerronWright.BrownianFirstPassageReflection
