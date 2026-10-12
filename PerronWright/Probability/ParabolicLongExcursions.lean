import PerronWright.Probability.FullHorizonExcursionComponents
import PerronWright.Probability.BrownianFullHorizonDrift

/-!
# Deterministic exclusion of late long parabolic excursions

Sublinear continuous noise forces a parabolic drift to fall below its
value a fixed positive time later at every sufficiently late time.
Actual running minima then exclude long reflected excursions beginning
late. Cofinal genuine return times bound their right endpoints uniformly.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ParabolicLongExcursions

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents BrownianWindowExcursions
open ContinuousPathReflection ReflectionExcursionReturns

theorem eventually_fixed_increment_negative {f : ℝ≥0 → ℝ}
    (hf : Tendsto (fun t : ℝ≥0 ↦ f t / (t : ℝ)) atTop (𝓝 0))
    (lambda : ℝ) (d : ℝ≥0) (hd : 0 < d) :
    ∃ T : ℝ≥0, ∀ s ≥ T,
      parabolicDrift lambda f (s+d) < parabolicDrift lambda f s := by
  have heps : (0 : ℝ) < (d : ℝ)/8 := div_pos hd (by norm_num)
  have hn : Tendsto (fun t : ℝ≥0 ↦ ‖f t / (t : ℝ)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hf.norm
  obtain ⟨A,hA⟩ := eventually_atTop.mp (hn.eventually (Iio_mem_nhds heps))
  let L : ℝ≥0 := ⟨2*|lambda|+1,by positivity⟩
  let T := max A (max 1 L)
  refine ⟨T,fun s hs ↦ ?_⟩
  have hsA : A ≤ s := (le_max_left _ _).trans hs
  have hs1 : (1 : ℝ≥0) ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hsL : L ≤ s := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs1
  have hsdpos : (0 : ℝ) < (s+d : ℝ≥0) := by simpa using add_pos_of_pos_of_nonneg hspos d.coe_nonneg
  have hsb : ‖f s‖ ≤ (d : ℝ)/8 * (s : ℝ) := by
    have h := (hA s hsA).le
    rw [norm_div,Real.norm_of_nonneg s.coe_nonneg] at h
    exact (div_le_iff₀ hspos).mp h
  have hsdb : ‖f (s+d)‖ ≤ (d : ℝ)/8 * (s+d : ℝ≥0) := by
    have h := (hA (s+d) (hsA.trans (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ d)))).le
    rw [norm_div,Real.norm_of_nonneg (s+d).coe_nonneg] at h
    exact (div_le_iff₀ hsdpos).mp h
  have hl : lambda ≤ |lambda| := le_abs_self lambda
  have hsl : 2*|lambda|+1 ≤ (s : ℝ) := hsL
  have hb0 := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hsb)).1
  have hb1 := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hsdb)).2
  change f (s+d) + lambda*((s : ℝ)+(d : ℝ)) - ((s : ℝ)+(d : ℝ))^2/2 <
    f s + lambda*(s : ℝ) - (s : ℝ)^2/2
  simp only [NNReal.coe_add] at hb1
  have hd' : (0 : ℝ) < d := hd
  nlinarith [sq_nonneg (d : ℝ)]

theorem runningMinimum_eq_left_of_positive {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {l v : ℝ≥0} (hlv : l ≤ v) (hl : reflected f l = 0)
    (hp : ∀ u ∈ Ioc l v, 0 < reflected f u) : runningMinimum f v = f l := by
  obtain ⟨u,hu,he⟩ := runningMinimum_attained hf v
  have hul : u ≤ l := by
    by_contra h
    have hz := reflected_zero_of_minimum_attained hf hu.2 he
    have hpos := hp u ⟨lt_of_not_ge h,hu.2⟩
    simp only [hz,lt_self_iff_false] at hpos
  have hm : runningMinimum f v = runningMinimum f l := by
    apply le_antisymm (runningMinimum_antitone hf hlv)
    rw [he]
    exact runningMinimum_le hf hul
  rw [hm]
  unfold reflected at hl
  linarith

theorem long_excursion_left_bounded (f : Path)
    (hf : Tendsto (fun t : ℝ≥0 ↦ f t / (t : ℝ)) atTop (𝓝 0))
    (lambda : ℝ) (hlim : Tendsto (driftPath lambda f) atTop atBot)
    (a : ℝ) (ha : 0 < a) :
    ∃ T : ℝ≥0, ∀ q : ℝ, q ∈ positiveSet (driftedReflectionPath lambda f) →
      a ≤ length q (driftedReflectionPath lambda f) →
      leftEndpoint q (driftedReflectionPath lambda f) < (T : ℝ) := by
  let d : ℝ≥0 := ⟨a/2,by positivity⟩
  have hd : 0 < d := by change (0 : ℝ) < a/2; positivity
  obtain ⟨T,hT⟩ := eventually_fixed_increment_negative hf lambda d hd
  refine ⟨T,fun q hq hlen ↦ ?_⟩
  let g := driftedReflectionPath lambda f
  have hb := reflection_component_bddAbove (driftPath lambda f) hlim q
  have hend := endpoint_bounds hq hb
  let l : ℝ≥0 := ⟨leftEndpoint q g,hend.1⟩
  let v := l+d
  have hvR : (v : ℝ) < rightEndpoint q g := by
    change leftEndpoint q g + a/2 < rightEndpoint q g
    change a ≤ rightEndpoint q g-leftEndpoint q g at hlen
    linarith
  have hl : reflected (driftPath lambda f) l = 0 := by
    have h := (reflection_endpoints_zero (driftPath lambda f) hlim hq).1
    change realEval g (leftEndpoint q g) = 0 at h
    rw [← show (l : ℝ) = leftEndpoint q g from rfl] at h
    simpa only [realEval,Real.toNNReal_coe,g,driftedReflectionPath,reflectionPath_apply] using h
  have hp : ∀ u ∈ Ioc l v, 0 < reflected (driftPath lambda f) u := by
    intro u hu
    have hc : (u : ℝ) ∈ component g q := by
      rw [component_eq_Ioo hq hb]
      have hlu : leftEndpoint q g < (u : ℝ) := hu.1
      have huv : (u : ℝ) ≤ v := hu.2
      exact ⟨hlu,huv.trans_lt hvR⟩
    have h := (component_subset g q hc).2
    change 0 < realEval g (u : ℝ) at h
    simpa only [realEval,Real.toNNReal_coe,g,driftedReflectionPath,reflectionPath_apply] using h
  have hmv := runningMinimum_eq_left_of_positive (continuous_path (driftPath lambda f))
    (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ d)) hl hp
  by_contra h
  have hs : T ≤ l := le_of_not_gt h
  have hfall := hT l hs
  have hpos := hp v ⟨lt_add_of_pos_right l hd,le_rfl⟩
  change 0 < driftPath lambda f v-runningMinimum (driftPath lambda f) v at hpos
  rw [hmv] at hpos
  change driftPath lambda f v < driftPath lambda f l at hfall
  linarith

/-- All sufficiently long genuine full excursions lie in one common
finite time window; both endpoint bounds are proved from the actual path. -/
theorem long_excursion_uniform_window (f : Path)
    (hf : Tendsto (fun t : ℝ≥0 ↦ f t / (t : ℝ)) atTop (𝓝 0))
    (lambda : ℝ) (hlim : Tendsto (driftPath lambda f) atTop atBot)
    (a : ℝ) (ha : 0 < a) :
    ∃ H : ℝ, 0 < H ∧ ∀ q : ℝ, q ∈ positiveSet (driftedReflectionPath lambda f) →
      a ≤ length q (driftedReflectionPath lambda f) →
      rightEndpoint q (driftedReflectionPath lambda f) < H ∧
      component (driftedReflectionPath lambda f) q ⊆ Ioo 0 H := by
  obtain ⟨T,hT⟩ := long_excursion_left_bounded f hf lambda hlim a ha
  obtain ⟨z,hTz,hz⟩ := exists_zero_after (continuous_path (driftPath lambda f)) hlim T
  let H := (z : ℝ)+1
  refine ⟨H,by dsimp [H]; positivity,fun q hq hlen ↦ ?_⟩
  let g := driftedReflectionPath lambda f
  have hb := reflection_component_bddAbove (driftPath lambda f) hlim q
  have hLz : leftEndpoint q g < (z : ℝ) := (hT q hq hlen).trans hTz
  have hRz : rightEndpoint q g ≤ (z : ℝ) := by
    by_contra h
    have hc : (z : ℝ) ∈ component g q := by
      rw [component_eq_Ioo hq hb]
      exact ⟨hLz,lt_of_not_ge h⟩
    have hp := (component_subset g q hc).2
    change 0 < realEval g (z : ℝ) at hp
    have hz' : realEval g (z : ℝ) = 0 := by
      simpa only [realEval,Real.toNNReal_coe,g,driftedReflectionPath,reflectionPath_apply] using hz
    simp only [hz',lt_self_iff_false] at hp
  have hRH : rightEndpoint q g < H := by dsimp [H]; linarith
  refine ⟨hRH,fun r hr ↦ ?_⟩
  have hri := hr
  rw [component_eq_Ioo hq hb] at hri
  exact ⟨(component_subset g q hr).1,hri.2.trans hRH⟩

end PerronWright.ParabolicLongExcursions
