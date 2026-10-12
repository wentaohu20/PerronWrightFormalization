import PerronWright.Probability.BrownianBridgeCyclicGeometry

/-! # Literal cyclic-bridge area identity

Translation and interval splitting prove that cyclic shift preserves
the integral before subtracting the starting value. At any interval
minimum the new area is the signed bridge area minus T times its
minimum, and is nonnegative. This is deterministic path geometry,
not a positive-excursion area distribution or Wright moment identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeCyclicArea

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeCycleKernel
open BrownianBridgeCyclicPath BrownianBridgeCyclicGeometry BrownianPinnedBridgeArea
open BrownianUniformQuadrature

private theorem integral_cyclic_splice (g : ℝ → ℝ) (hg : Continuous g)
    (T s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ T) (he : g T = g 0) :
    (∫ t in 0..T, if s+t ≤ T then g (s+t) else g (s+t-T)) = ∫ t in 0..T, g t := by
  let v : ℝ → ℝ := fun t ↦ if s+t ≤ T then g (s+t) else g (s+t-T)
  have hp : Continuous (fun t : ℝ ↦ s+t) := continuous_const.add continuous_id
  have hm : Continuous (fun t : ℝ ↦ s+t-T) := hp.sub continuous_const
  have hv : Continuous v := (hg.comp hp).if_le (hg.comp hm) hp
    (continuous_const : Continuous (fun _ : ℝ ↦ T)) (fun t ht ↦ by simp only [Function.comp_apply,ht,sub_self,he])
  have hl : (∫ t in 0..T-s, v t) = ∫ t in 0..T-s, g (s+t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 (T-s) := by
      simpa only [uIcc_of_le (sub_nonneg.mpr hs)] using ht
    simp only [v,if_pos (show s+t ≤ T by linarith [ht'.2])]
  have hr : (∫ t in T-s..T, v t) = ∫ t in T-s..T, g (s+t-T) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith : T-s ≤ T)
    intro t ht
    simp only [v,if_neg (show ¬s+t ≤ T by linarith [ht.1])]
  change (∫ t in 0..T, v t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hv.intervalIntegrable 0 (T-s)) (hv.intervalIntegrable (T-s) T),
    hl,hr,intervalIntegral.integral_comp_add_left]
  have hshift : (fun t : ℝ ↦ g (s+t-T)) = fun t ↦ g (t+(s-T)) := by
    funext t
    congr 1
    ring
  rw [hshift,intervalIntegral.integral_comp_add_right]
  have h1 : s+0=s := add_zero s
  have h2 : s+(T-s)=T := by ring
  have h3 : T-s+(s-T)=0 := by ring
  have h4 : T+(s-T)=s := by ring
  rw [h1,h2,h3,h4,add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 s) (hg.intervalIntegrable s T)]

def closedArea (T : ℝ≥0) (f : Path) : ℝ :=
  ∫ t in 0..(T : ℝ), closedBridge T (Real.toNNReal t) f

def pathArea (T : ℝ≥0) (f : Path) : ℝ := ∫ t in 0..(T : ℝ), f (Real.toNNReal t)

def pathQuadrature (T : ℝ≥0) (m : ℕ) (f : Path) : ℝ :=
  leftSum (T : ℝ) m (fun t ↦ f (Real.toNNReal t))

theorem continuous_pathQuadrature (T : ℝ≥0) (m : ℕ) : Continuous (pathQuadrature T m) := by
  unfold pathQuadrature leftSum
  exact continuous_finsetSum _ (fun i _ ↦ (continuous_eval (Real.toNNReal (grid T m i))).const_mul _)

theorem pathQuadrature_tendsto_pathArea (T : ℝ≥0) (f : Path) :
    Tendsto (fun n : ℕ ↦ pathQuadrature T (n+1) f) atTop (𝓝 (pathArea T f)) :=
  leftSum_tendsto_integral T T.coe_nonneg _ ((continuous_path f).comp continuous_real_toNNReal)

theorem measurable_pathArea (T : ℝ≥0) : Measurable (pathArea T) :=
  measurable_of_tendsto_metrizable (fun n ↦ (continuous_pathQuadrature T (n+1)).measurable)
    (tendsto_pi_nhds.mpr (pathQuadrature_tendsto_pathArea T))

theorem closedArea_eq_pathArea (T : ℝ≥0) (f : Path) :
    closedArea T f = pathArea T (stoppedClosedBridgePath T f) := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc 0 (T : ℝ) := by simpa only [uIcc_of_le T.coe_nonneg] using ht
  have htNN : Real.toNNReal t ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht'.2
  change closedBridge T (Real.toNNReal t) f = closedBridge T (min (Real.toNNReal t) T) f
  rw [min_eq_left htNN]

theorem measurable_closedArea (T : ℝ≥0) : Measurable (closedArea T) := by
  have he : closedArea T = pathArea T ∘ stoppedClosedBridgePath T :=
    funext (closedArea_eq_pathArea T)
  rw [he]
  exact (measurable_pathArea T).comp (measurable_stoppedClosedBridgePath T)

theorem ae_closedArea_eq_area (T : ℝ≥0) : closedArea T =ᵐ[pathLaw] area T := by
  filter_upwards [ae_closedBridge_eq_bridge T] with f hf
  exact intervalIntegral.integral_congr (fun _ _ ↦ hf _)

theorem cyclicValue_real (T s : ℝ≥0) (f : Path) (t : ℝ) (ht : 0 ≤ t) :
    cyclicValue T s (Real.toNNReal t) f =
      (if (s : ℝ)+t ≤ (T : ℝ) then closedBridge T (Real.toNNReal ((s : ℝ)+t)) f
       else closedBridge T (Real.toNNReal ((s : ℝ)+t-(T : ℝ))) f)-closedBridge T s f := by
  unfold cyclicValue
  have he : cycleTime T s (Real.toNNReal t) = Real.toNNReal (realCycleTime T s t) := by
    have hr : (cycleTime T s (Real.toNNReal t) : ℝ) = realCycleTime T s t := by
      simpa only [Real.coe_toNNReal t ht] using cycleTime_real T s (Real.toNNReal t)
    rw [← hr,Real.toNNReal_coe]
  rw [he]
  unfold realCycleTime
  split_ifs <;> rfl

theorem pathArea_cyclicBridgePath (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) (f : Path) :
    pathArea T (cyclicBridgePath T hT s f) = closedArea T f-(T : ℝ)*closedBridge T s f := by
  let g : ℝ → ℝ := fun t ↦ closedBridge T (Real.toNNReal t) f
  have hg : Continuous g := (continuous_sample_closedBridge T f).comp continuous_real_toNNReal
  let v : ℝ → ℝ := fun t ↦ if (s : ℝ)+t ≤ T then g ((s : ℝ)+t) else g ((s : ℝ)+t-T)
  have hp : Continuous (fun t : ℝ ↦ (s : ℝ)+t) := continuous_const.add continuous_id
  have hm : Continuous (fun t : ℝ ↦ (s : ℝ)+t-T) := hp.sub continuous_const
  have he : g T=g 0 := by simp only [g,Real.toNNReal_coe,Real.toNNReal_zero,
    closedBridge_endpoint T hT f,closedBridge_zero]
  have hv : Continuous v := (hg.comp hp).if_le (hg.comp hm) hp
    (continuous_const : Continuous (fun _ : ℝ ↦ (T : ℝ)))
    (fun t ht ↦ by simp only [Function.comp_apply,ht,sub_self,he])
  have hc : pathArea T (cyclicBridgePath T hT s f) =
      ∫ t in 0..(T : ℝ), v t-closedBridge T s f := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 (T : ℝ) := by simpa only [uIcc_of_le T.coe_nonneg] using ht
    have htNN : Real.toNNReal t ≤ T := (Real.toNNReal_le_iff_le_coe).mpr ht'.2
    change cyclicValue T s (min (Real.toNNReal t) T) f = _
    rw [min_eq_left htNN,cyclicValue_real T s f t ht'.1]
  rw [hc,intervalIntegral.integral_sub (hv.intervalIntegrable 0 T)
    (continuous_const.intervalIntegrable 0 T),
    intervalIntegral.integral_const]
  have hsp := integral_cyclic_splice g hg (T : ℝ) (s : ℝ) s.coe_nonneg hs he
  change (∫ t in 0..(T : ℝ), v t)-((T : ℝ)-0) • closedBridge T s f = _
  rw [hsp]
  simp only [sub_zero,smul_eq_mul,closedArea,g]

theorem minimum_shift_area_nonneg (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) (f : Path)
    (hm : ∀ t : ℝ≥0, t ≤ T → closedBridge T s f ≤ closedBridge T t f) :
    0 ≤ closedArea T f-(T : ℝ)*closedBridge T s f := by
  rw [← pathArea_cyclicBridgePath T s hT hs f]
  exact intervalIntegral.integral_nonneg_of_forall T.coe_nonneg
    (fun t ↦ cyclicBridgePath_nonneg_of_minimizer T s hT hs f hm _)

/-- On the actual Brownian driver, cyclic area is exactly signed pinned
area minus T times the literal pinned value at the shift, simultaneously
for all shifts. No positive-excursion law is substituted. -/
theorem ae_pathArea_cyclicBridgePath (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, ∀ s : ℝ≥0, s ≤ T →
      pathArea T (cyclicBridgePath T hT s f) = area T f-(T : ℝ)*bridge T s f := by
  filter_upwards [ae_closedArea_eq_area T,ae_closedBridge_eq_bridge T] with f ha hb
  intro s hs
  rw [pathArea_cyclicBridgePath T s hT hs f,ha,hb]

end PerronWright.BrownianBridgeCyclicArea
